{-# LANGUAGE StrictData #-}
module Flow.CopyAnalysis
    ( writePathAnalysis
    , emptyEnv, emptyFunInfo
    , WriteTarget(..), PrimitiveWriteTarget(..)
    , CopyAllowed(..), WriteOccured(..)
    , Position(..)
    , argumentDependency
    , Error(..), ErrorMessage(..), prettyCopyError, prettyErrorMessage
    , runAnalysisM
    )
where

import Types.Annotation
import Types.Ast
import Types.Common
import Types.Types

import Control.Monad.Except
import Control.Monad.State
import Data.Bifunctor
import Data.Functor.Identity
import Data.List (foldl', sortOn, nub, find)
import Data.Maybe
import Data.Monoid
import qualified Data.Generics as G
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S
import qualified Data.Text as T

import Debug.Trace

data Error
    = Error
    { e_pos :: Pos
    , e_error :: ErrorMessage
    } deriving (Eq, Ord, Show)

instance Monoid Error where
    mempty = Error (Pos "<unknown>" Nothing Nothing) ENoError
    mappend _ b = b

prettyCopyError :: Error -> T.Text
prettyCopyError e =
    "Error on " <> T.pack (show $ e_pos e) <> ": \n"
    <> prettyErrorMessage (e_error e)

data ErrorMessage
    = ECantCopy Var [RecordKey]
    | ENoError
    deriving (Eq, Ord, Show)

prettyErrorMessage :: ErrorMessage -> T.Text
prettyErrorMessage em =
    case em of
      ENoError -> "No error"
      ECantCopy (Var v) keys ->
          "Can not copy " <> v <> keyPath keys
    where
      keyPath ks =
          "." <> T.intercalate "." (map unRecordKey ks)

data AnalysisState
    = AnalysisState
    { as_varSupply :: Int
    } deriving (Show, Eq, Ord)

initAnalysisState :: AnalysisState
initAnalysisState = AnalysisState 0

freshVar :: AnalysisM m => m Var
freshVar =
    do s <- get
       put $ s { as_varSupply = as_varSupply s + 1 }
       pure $ Var $ T.pack $ "internal" ++ show (as_varSupply s)

type AnalysisM m = (MonadPlus m, MonadError Error m, MonadState AnalysisState m)
runAnalysisM :: ExceptT Error (StateT AnalysisState Identity) a -> Either Error a
runAnalysisM action = runIdentity $ evalStateT (runExceptT action) initAnalysisState

data CopyAllowed
    = CaAllowed
    | CaBanned
    deriving (Show, Eq)

data WriteOccured
    = WoWrite
    | WoRead
    deriving (Show, Eq)

data Position
    = PIn
    | POut
    | PInOut
    deriving (Show, Eq)

data PrimitiveWriteTarget
    = PwtVar Var [RecordKey] CopyAllowed WriteOccured Position
    | PwtNone
    deriving (Show, Eq)

data WriteTarget
    = WtPrim PrimitiveWriteTarget
    | WtMany [PrimitiveWriteTarget]
    deriving (Show, Eq)

data CopySide
    = CsLeft
    | CsRight
    deriving (Show, Eq)

data CopyAction
    = CopyAction
    { ca_var :: Var
    , ca_path :: [RecordKey]
    , ca_side :: CopySide
    } deriving (Show, Eq)

makeAccessExpr :: Pos -> CopyAction -> Expr TypedPos
makeAccessExpr pos ca =
    injectPath (ca_path ca) $ EVar (Annotated ann (ca_var ca))
    where
      ann = TypedPos pos t
      t = TVar (TypeVar "<unknown>")
      injectPath remaining inner =
          case remaining of
            [] -> inner
            (rk:more) ->
                injectPath more $
                ERecordAccess $ Annotated ann $
                RecordAccess inner rk

applyCopyActions ::
    (AnalysisM m, Show w, Applyable w, Applyable v) => [CopyAction] -> w -> v
    -> m (Expr TypedPos -> Expr TypedPos, w, v)
applyCopyActions cas =
    loop cas id
    where
      loop actions bind l r =
          case actions of
            [] -> pure (bind, l, r)
            (ca:more) ->
                do (bind', l', r') <- applyCopyAction ca l r
                   loop more (bind . bind') l' r'

applyCopyAction ::
    (AnalysisM m, Show w, Applyable w, Applyable v) => CopyAction -> w -> v
    -> m (Expr TypedPos -> Expr TypedPos, w, v)
applyCopyAction ca lhs rhs =
    case ca_side ca of
      CsLeft ->
          do (lhs', bind) <- applyAnywhere ca lhs
             pure $ trace ("Apply " ++ show ca ++ " to " ++ show lhs ++ "=> \n" ++ show lhs') (bind, lhs', rhs)
      CsRight ->
          do (rhs', bind) <- applyAnywhere ca rhs
             pure (bind, lhs, rhs')

applyAnywhere ::
    (AnalysisM m, Applyable w)
    => CopyAction -> w -> m (w, Expr TypedPos -> Expr TypedPos)
applyAnywhere copyAction target =
    runStateT (applyCa copyAction target) id

class Applyable x where
    applyCa :: AnalysisM m => CopyAction -> x -> StateT (Expr TypedPos -> Expr TypedPos) m x

instance Applyable (Expr TypedPos) where
    applyCa = applyCollecting

instance Applyable (Maybe (Expr TypedPos), Expr TypedPos) where
    applyCa ca (a, b) =
        do r <- applyCa ca a
           s <- applyCa ca b
           pure (r, s)

instance Applyable x => Applyable [x] where
    applyCa ca x = forM x (applyCa ca)

instance Applyable x => Applyable (Maybe x) where
    applyCa ca x = forM x (applyCa ca)

applyCollecting ::
    AnalysisM m
    => CopyAction -> Expr TypedPos -> StateT (Expr TypedPos -> Expr TypedPos) m (Expr TypedPos)
applyCollecting ca expr =
    trace ("!!! Applying " ++ show ca ++ " to: \n" ++ show expr) $
    do (bind, e') <- lift $ applySingleCopyAction ca expr
       modify' $ \oldBind -> oldBind . bind -- TODO: is this order correct???
       pure e'

applySingleCopyAction ::
    AnalysisM m => CopyAction -> Expr TypedPos -> m (Expr TypedPos -> Expr TypedPos, Expr TypedPos)
applySingleCopyAction ca expr =
    do bindVar <- freshVar
       let exprAnn = getExprAnn expr
           pos = tp_pos exprAnn
           ann = TypedPos pos (TVar (TypeVar "<unknown>"))
           boundVar =
               Annotated ann bindVar
           boundExpr =
               ECopy searchExpr
           searchExpr = makeAccessExpr pos ca
           replaceExpr = EVar boundVar
           clobberAnnotation :: Expr TypedPos -> Expr TypedPos
           clobberAnnotation e =
               let clobber (TypedPos _ _) = ann
               in G.everywhere (G.mkT clobber) e
           clobberedSearch = clobberAnnotation searchExpr
           execReplace e =
               let clobbered = clobberAnnotation e
               in if clobbered == clobberedSearch
                  then replaceExpr
                  else e
       let bind x =
               ELet $ Annotated exprAnn $ Let boundVar boundExpr x
       pure (bind, G.everywhere (G.mkT execReplace) expr)

joinWritePaths :: AnalysisM m => Pos -> WriteTarget -> WriteTarget -> m (WriteTarget, [CopyAction])
joinWritePaths pos w1 w2 =
    case (w1, w2) of
      (WtPrim PwtNone, x) -> pure (x, mempty)
      (x, WtPrim PwtNone) -> pure (x, mempty)
      (WtPrim x, WtPrim y) -> first (packMany . map WtPrim) <$> handleTargets pos [x] [y]
      (WtPrim x, WtMany y) -> first (packMany . map WtPrim) <$> handleTargets pos [x] y
      (WtMany x, WtPrim y) -> first (packMany . map WtPrim) <$> handleTargets pos x [y]
      (WtMany x, WtMany y) -> first (packMany . map WtPrim) <$> handleTargets pos x y

type TargetTuple = (Var, [RecordKey], CopyAllowed, WriteOccured, Position)

shortestVarPath :: [TargetTuple] -> Maybe TargetTuple
shortestVarPath tts =
    case sortOn (\(_, rks, _, _, _) -> length rks) tts of
      [] -> Nothing
      (t : _) -> Just t

copyActionGen :: Bool -> [TargetTuple] -> CopySide -> Maybe CopyAction
copyActionGen needsWrite tts cs =
    fmap mkCopy $ propagationVal needsWrite tts
    where
      mkCopy (v, rks, _, _, _) =
          CopyAction v rks cs

propagationVal :: Bool -> [TargetTuple] -> Maybe TargetTuple
propagationVal needsWrite tts =
    shortestVarPath $ if needsWrite then filter writes tts else tts

writes :: TargetTuple -> Bool
writes (_, _, _, wo, _) = wo == WoWrite

handleTargets ::
    forall m. AnalysisM m
    => Pos
    -> [PrimitiveWriteTarget]
    -> [PrimitiveWriteTarget]
    -> m ([PrimitiveWriteTarget], [CopyAction])
handleTargets pos lhs rhs =
    do let folder hm pwt =
               case pwt of
                 PwtNone -> hm
                 PwtVar x rk ca wo p -> HM.insertWith (++) x [(x, rk, ca, wo, p)] hm
           makeByVar = foldl' folder mempty
           byVar =
               let l = HM.map (\x -> (x, mempty)) $ makeByVar lhs
                   r = HM.map (\x -> (mempty, x)) $ makeByVar rhs
               in HM.elems $ HM.unionWith (\(a, b) (x, y) -> (a ++ x, b ++ y)) l r
           repack (x, rk, ca, wo, p) = PwtVar x rk ca wo p
           allowsCopy (_, _, ca, _, _) = ca == CaAllowed
           propAny r = maybeToList $ propagationVal False r
           handlePair ::
               ([TargetTuple], [CopyAction])
               -> ([TargetTuple], [TargetTuple])
               -> m ([TargetTuple], [CopyAction])
           handlePair (writeTargets, copyActions) p =
               case p of
                 (l, []) -> pure (writeTargets ++ propAny l,  copyActions)
                 ([], r) -> pure (writeTargets ++ propAny r, copyActions)
                 (l, r)
                     | all (not . writes) l ->
                       do let interestingR = propAny r
                          pure
                              ( writeTargets ++ interestingR
                              , copyActions
                              )
                     | otherwise ->
                           do let canCopyL = all allowsCopy l
                                  canCopyR = all allowsCopy r
                                  writesL = any writes l
                                  writesR = any writes r
                                  (var, rks, _, _, _) =
                                      fromJust $
                                      propagationVal True (l ++ r)
                              case (canCopyL, canCopyR) of
                                (False, False) ->
                                    throwError $ Error pos $ ECantCopy var rks
                                (True, _) ->
                                    pure
                                        ( writeTargets ++ maybeToList (propagationVal writesR r)
                                        , copyActions
                                            ++ maybeToList (copyActionGen writesL l CsLeft)
                                        )
                                (_, True) ->
                                    pure
                                        ( writeTargets ++ maybeToList (propagationVal writesL l)
                                        , copyActions
                                            ++ maybeToList (copyActionGen writesR r CsRight)
                                        )

       first (map repack) <$> foldM handlePair (mempty, mempty) byVar

packMany :: [WriteTarget] -> WriteTarget
packMany wts =
    case wts of
      [] -> WtPrim PwtNone
      [x] -> x
      many ->
          let merged = foldl' merge mempty many
          in case nub merged of
              [] -> WtPrim PwtNone
              [x] -> WtPrim x
              xs -> WtMany xs
    where
      merge accum wtgt =
          case wtgt of
            WtPrim PwtNone -> accum
            WtPrim pwt -> accum <> [pwt]
            WtMany pwts -> accum <> pwts

data FunType
    = FtFun [Maybe (Var, [RecordKey], CopyAllowed, WriteOccured, Position)]
    | FtRec (Record FunType)
    | FtSelf
    deriving (Show, Eq)

newtype FunInfo
    = FunInfo { unFunInfo :: HM.HashMap Var FunType }
    deriving (Show, Eq)

emptyFunInfo :: FunInfo
emptyFunInfo = FunInfo mempty

pathLookup :: [RecordKey] -> FunType -> Maybe FunType
pathLookup =
    go
    where
      go path ty =
          case path of
            [] -> Just ty
            (x:xs) ->
                case ty of
                  FtFun _ -> error "Internal inconsisency"
                  FtSelf -> error "Shouldn't happen"
                  FtRec (Record hm) ->
                      case HM.lookup x hm of
                        Nothing -> Nothing
                        Just fty -> go xs fty

getFunType :: AnalysisM m => Expr TypedPos -> FunInfo -> m (Maybe FunType)
getFunType expr funInfo =
    case expr of
      ELambda (Annotated _ lambda) -> Just . FtFun <$> argumentDependency funInfo lambda
      EVar (Annotated _ var) -> pure $ HM.lookup var (unFunInfo funInfo)
      ERecordAccess (Annotated _ (RecordAccess r rk)) ->
          getFunType r funInfo >>= \res ->
          case res of
            Nothing -> pure Nothing
            Just ft -> pure $ pathLookup [rk] ft
      ERecord (Annotated _ record) ->
          Just . FtRec <$> recordMapMaybeM (\e -> getFunType e funInfo) record
      EFunApp (Annotated _ (FunApp rcvE _)) ->
          getFunType rcvE funInfo
      _ -> pure Nothing -- TODO: is this right??

funWriteThrough ::
    forall m. AnalysisM m
    => [Maybe (Var, [RecordKey], CopyAllowed, WriteOccured, Position)]
    -> [Expr TypedPos]
    -> FunInfo
    -> m (WriteTarget, [Expr TypedPos])
funWriteThrough funType args funInfo =
    do targets <- mapM (uncurry makeTarget) (zip funType args)
       pure (packMany $ fmap fst targets, fmap snd targets)
    where
      makeTarget ::
          Maybe (Var, [RecordKey], CopyAllowed, WriteOccured, Position)
          -> Expr TypedPos
          -> m (WriteTarget, Expr TypedPos)
      makeTarget mArgTy arg =
          case mArgTy of
            Nothing ->
                pure (WtPrim PwtNone, arg)
            Just (_, keys, copyAllowed, wo, pos) ->
                writePathAnalysis arg (Env keys funInfo copyAllowed wo pos)

data Env
    = Env
    { e_pathTraversed :: [RecordKey]
    , e_funInfo :: FunInfo
    , e_copyAllowed :: CopyAllowed
    , e_writeOccured :: WriteOccured
    , e_position :: Position
    } deriving (Show, Eq)

emptyEnv :: Env
emptyEnv = Env [] emptyFunInfo CaAllowed WoRead PInOut

handleBinOp :: AnalysisM m => Env -> TypedPos -> BinOp TypedPos -> m (WriteTarget, Expr TypedPos)
handleBinOp env tp@(TypedPos pos _) bo =
    case bo of
      BoAdd x y -> handleBo BoAdd x y
      BoSub x y -> handleBo BoSub x y
      BoMul x y -> handleBo BoMul x y
      BoDiv x y -> handleBo BoDiv x y
      BoEq x y -> handleBo BoEq x y
      BoNeq x y -> handleBo BoNeq x y
      BoAnd x y -> handleBo BoAnd x y
      BoOr x y -> handleBo BoOr x y
      BoNot e ->
          do (wt, e') <- writePathAnalysis e env
             pure (wt, addA $ BoNot e')
    where
      addA = EBinOp . Annotated tp
      handleBo c x y =
          do (lhs, le) <- writePathAnalysis x env
             (rhs, re) <- writePathAnalysis y env
             (writeTarget, copyActions) <- joinWritePaths pos lhs rhs
             (bind, l, r) <- applyCopyActions copyActions le re
             pure (writeTarget, bind $ addA (c l r))

type BranchSwitch = (Maybe (Expr TypedPos), Expr TypedPos)

handleBranchSwitch ::
    AnalysisM m
    => Env
    -> TypedPos
    -> BranchSwitch
    -> m (WriteTarget, BranchSwitch, Expr TypedPos -> Expr TypedPos)
handleBranchSwitch env (TypedPos pos _) (mCondE, bodyE) =
    case mCondE of
      Nothing ->
          do (wt, e') <- writePathAnalysis bodyE env
             pure (wt, (Nothing, e'), id)
      Just condE ->
          trace ("BranchSwitch condE=" ++ show condE ++ " pathTraversed=" ++ show (e_pathTraversed env)) $
          do (condWt, condE') <-
                 writePathAnalysis condE $
                 env
                 { e_pathTraversed = []
                 , e_position = PIn
                 }
             (bodyWt, bodyE') <- writePathAnalysis bodyE env
             (writeTarget, copyActions) <- joinWritePaths pos condWt bodyWt
             (bind, l, r) <- applyCopyActions copyActions condE' bodyE'
             pure (writeTarget, (Just l, r), bind)

handleBranchSwitchPair ::
    (AnalysisM m, Show w, Applyable w)
    => Env
    -> TypedPos
    -> (WriteTarget, w, Expr TypedPos -> Expr TypedPos)
    -> BranchSwitch
    -> m (WriteTarget, w, BranchSwitch, Expr TypedPos -> Expr TypedPos)
handleBranchSwitchPair env tp@(TypedPos pos _) (wtL, l1, bindL) r =
    do (wtR, r1, bindR) <- handleBranchSwitch env tp r
       (writeTarget, copyActions) <- joinWritePaths pos wtL wtR
       (bind3, bs1, bs2) <-
           applyCopyActions copyActions l1 r1
       let binds =
               bindL . bindR . bind3
       pure (writeTarget, bs1, bs2, binds)

handleBranchSwitchSequence ::
    forall m. AnalysisM m
    => Env
    -> TypedPos
    -> [BranchSwitch]
    -> m (WriteTarget, [BranchSwitch], Expr TypedPos -> Expr TypedPos)
handleBranchSwitchSequence env tp branches =
    do let looper st [] = pure st
           looper (oldWt, oldEs, oldBind) (b:bs) =
               do (wt, newEs, b', newBind) <-
                      handleBranchSwitchPair env tp (oldWt, oldEs, oldBind) b
                  looper (wt, newEs ++ [b'], newBind) bs
       case branches of
         [] -> error "Missing branches, requiring branches for this analysis"
         (b1:rest) ->
             do (wt, bs, bind) <- handleBranchSwitch env tp b1
                looper (wt, [bs], bind) rest

handleIf :: AnalysisM m => Env -> TypedPos -> If TypedPos -> m (WriteTarget, Expr TypedPos)
handleIf env tp (If bodies elseExpr) =
    do let inputBranches =
               map (\(x, y) -> (Just x, y)) bodies
               ++ [(Nothing, elseExpr)]
       (wt, branches, bind) <- handleBranchSwitchSequence env tp inputBranches
       let collectBodies xs =
               case xs of
                 [] -> []
                 ((Just cond, body) : more) -> ((cond, body) : collectBodies more)
                 ((Nothing, _) : more) -> collectBodies more
           bodies' = collectBodies branches
           elseExpr' =
               case find (\(x, _) -> isNothing x) branches of
                  Nothing -> error "Internal inconsistency error"
                  Just (_, e) -> e
       pure (wt, bind $ addA $ If bodies' elseExpr')
    where
        addA = EIf . Annotated tp

handleCase :: AnalysisM m => Env -> TypedPos -> Case TypedPos -> m (WriteTarget, Expr TypedPos)
handleCase env tp (Case matchOn cases) =
    case cases of
      [] -> writePathAnalysis matchOn $ env { e_pathTraversed = [], e_position = PIn }
      (firstCase:otherCases) ->
          do let inputBranches =
                     ((Just matchOn, snd firstCase) : map (\(_, x) -> (Nothing, x)) otherCases)
             (wt, branches, bind) <- handleBranchSwitchSequence env tp inputBranches
             let matchOn' =
                     case find (\(x, _) -> isJust x) branches of
                       Just (Just m, _) -> m
                       _ -> error "Internal inconsistency error (2)"
                 cases' = zip (map fst cases) (map snd branches)
             pure (wt, bind $ addA $ Case matchOn' cases')
    where
      addA = ECase . Annotated tp

handleExprSequence ::
    AnalysisM m => Env -> TypedPos -> [Expr TypedPos]
    -> m (WriteTarget, [Expr TypedPos], Expr TypedPos -> Expr TypedPos)
handleExprSequence env (TypedPos pos _) exprs =
    case exprs of
      [] -> pure (WtPrim PwtNone, mempty, id)
      (x:xs) ->
          do (wt, x') <- writePathAnalysis x env
             looper (wt, [x'], id) xs
    where
      looper st [] = pure st
      looper (oldWt, oldX, oldBind) (y:ys) =
          do (wt, y') <- writePathAnalysis y env
             (wt', copyActions) <-
                 trace ("Joining: " ++ show oldWt ++ " with " ++ show wt) $
                 joinWritePaths pos oldWt wt
             (bind, oldX', y'') <-
                 trace ("CopyActions: " ++ show copyActions) $
                 applyCopyActions copyActions oldX y'
             looper (wt', oldX' ++ [y''], oldBind . bind) ys

handleList ::
    AnalysisM m => Env -> TypedPos -> [Expr TypedPos] -> m (WriteTarget, Expr TypedPos)
handleList env tp exprs =
    do (wt, exprs', bind) <- handleExprSequence env tp exprs
       pure (wt, bind $ addA exprs')
    where
        addA = EList . Annotated tp

handleRecord ::
    AnalysisM m => Env -> TypedPos -> Record (Expr TypedPos) -> m (WriteTarget, Expr TypedPos)
handleRecord env tp (Record hm) =
    do let kvList = HM.toList hm
       (wt, vals, bind) <- handleExprSequence env tp (map snd kvList)
       let record = Record $ HM.fromList $ zip (map fst kvList) vals
       pure (wt, bind $ addA record)
    where
      addA = ERecord . Annotated tp

handleRecordMerge ::
    AnalysisM m => Env -> TypedPos -> RecordMerge TypedPos -> m (WriteTarget, Expr TypedPos)
handleRecordMerge env tp@(TypedPos pos _) (RecordMerge tgt x noCopy) =
    do let env' =
               env
               { e_pathTraversed = []
               }
       (wtTgt, tgt') <-
           writePathAnalysis tgt $
           env'
           { e_copyAllowed = if not noCopy then CaAllowed else CaBanned
           , e_writeOccured = WoWrite
           }
       (wtX, x', bind) <- handleExprSequence (env' { e_position = PIn }) tp x
       (finalWt, copyActions) <- joinWritePaths pos wtTgt wtX
       (finalBind, tgt'', x'') <- applyCopyActions copyActions tgt' x'
       let allBinds = bind . finalBind
       pure (finalWt, allBinds $ addA (RecordMerge tgt'' x'' noCopy))
    where
        addA = ERecordMerge . Annotated tp

writePathAnalysis ::
    forall m. AnalysisM m
    => Expr TypedPos -> Env
    -> m (WriteTarget, Expr TypedPos)
writePathAnalysis expr env =
    case expr of
      ECopy _ -> pure $ unchanged $ WtPrim PwtNone -- should never happen
      ELit _ -> pure $unchanged $ WtPrim PwtNone -- does not do anything
      EList (Annotated pos list) -> handleList env pos list
      ERecord (Annotated pos r) -> handleRecord env pos r
      EBinOp (Annotated pos bo) -> handleBinOp env pos bo
      ELambda (Annotated ann (Lambda args body)) ->
          -- TODO: is this correct? Probably need to remove the targets
          -- that the arguments already handle.
          do (wt', body') <- writePathAnalysis body env
             pure (wt', ELambda (Annotated ann (Lambda args body')))
      EVar (Annotated _ var) ->
          pure $ unchanged $
          WtPrim $
          PwtVar var (e_pathTraversed env) (e_copyAllowed env) (e_writeOccured env) (e_position env)
      ERecordMerge (Annotated ann rm) -> handleRecordMerge env ann rm
      ERecordAccess (Annotated ann (RecordAccess r rk)) ->
          trace ("RecordAccess r=" ++ show r ++ " rk=" ++ show rk) $
          do (wt', r') <-
                 writePathAnalysis r $ env { e_pathTraversed = e_pathTraversed env ++ [rk] }
             pure (wt', ERecordAccess $ Annotated ann (RecordAccess r' rk))
      EIf (Annotated pos ifE) -> handleIf env pos ifE
      ECase (Annotated pos caseE) -> handleCase env pos caseE
      EFunApp (Annotated ann (FunApp rcvE args)) ->
          getFunType rcvE (e_funInfo env) >>= \funType ->
          case funType of
            Nothing -> error "Can't call function"
            Just FtSelf ->
                pure $ unchanged $ WtPrim PwtNone -- don't care about writes to self
            Just (FtFun ft) ->
                -- TODO: this is wrong, fix it!
                do (wt, args') <- funWriteThrough ft args (e_funInfo env)
                   pure (wt, EFunApp $ Annotated ann (FunApp rcvE args'))
            Just (FtRec r) -> error ("IMPLEMENT ME" ++ show r)
      ELet (Annotated ann1 (Let (Annotated ann2 var) bindE inE)) ->
          do let tempFunInfo =
                     FunInfo $ HM.insert var FtSelf (unFunInfo $ e_funInfo env)
             funInfo' <-
                 getFunType bindE tempFunInfo >>= \funType ->
                 case funType of
                   Nothing -> pure $ e_funInfo env
                   Just fi -> pure $ FunInfo $ HM.insert var fi (unFunInfo $ e_funInfo env)
             (bindWt, bindE') <-
                 -- TODO: this seems incorrect.
                 writePathAnalysis bindE $ env { e_funInfo = funInfo' }
             (resWt, bindE'', inE'') <-
                 do (inRes, inE') <- writePathAnalysis inE $ env { e_funInfo = funInfo' }
                    (retWt, bindE'') <-
                        handleLetTarget var bindE' (e_pathTraversed env) [] funInfo' inRes
                    pure (retWt, bindE'', inE')
             let let' =
                     ELet $ Annotated ann1 $ Let (Annotated ann2 var) bindE'' inE''
             pure (packMany [resWt, bindWt], let') -- NB: putting the resWt first here is important.
    where
      unchanged x = (x, expr)

handleLetTarget ::
    AnalysisM m
    => Var -> Expr TypedPos
    -> [RecordKey] -> [RecordKey]
    -> FunInfo -> WriteTarget
    -> m (WriteTarget, Expr TypedPos)
handleLetTarget var bindE pathTraversed pExtra funInfo wtarget =
    case wtarget of
      WtPrim (PwtVar v recordPath ca wo pos) | v == var && pos /= PIn ->
        writePathAnalysis bindE (Env pathTraversed funInfo ca wo pos) >>= \(wpRes, wpE) ->
        trace ("WPA wpRes=" ++ show wpRes) $
        case wpRes of
          WtPrim (PwtVar v2 rp2 ca2 wo2 p) | p /= PIn ->
              pure (WtPrim (PwtVar v2 (rp2 <> recordPath) ca2 wo2 p), wpE)
          WtMany wTargets ->
              do r <-
                     mapM (handleLetTarget var wpE pathTraversed recordPath funInfo . WtPrim)
                       wTargets
                 let outE =
                         case r of
                           [] -> wpE
                           (x:_) -> snd x
                 pure (packMany $ fmap fst r, outE)
          z -> pure (z, wpE)
      WtPrim (PwtVar v rp x y pos) | pos /= PIn ->
          pure (WtPrim (PwtVar v (rp <> pExtra) x y pos), bindE)
      WtPrim _ ->
          pure (WtPrim PwtNone, bindE)
      WtMany wTargets ->
          do r <-
                 mapM (handleLetTarget var bindE pathTraversed pExtra funInfo . WtPrim) wTargets
             let outE =
                     case r of
                       [] -> bindE
                       (x:_) -> snd x
             pure (packMany $ fmap fst r, outE)

-- | Given a lambda, infer which arguments
-- would need to be considered written if the result is written
argumentDependency ::
    AnalysisM m
    => FunInfo
    -> Lambda TypedPos
    -> m [Maybe (Var, [RecordKey], CopyAllowed, WriteOccured, Position)]
argumentDependency funInfo (Lambda args body) =
    do targets <-
           handleTarget . fst <$>
           writePathAnalysis body (Env [] funInfo CaAllowed WoRead PInOut)
       pure $
           trace ("Trace=" ++ show targets ++ " args=" ++ show args) $
           fmap (makeEntry targets . a_value) args
    where
      makeEntry targets var =
          let relevantTarget =
                  filter (\(v, _, _, wo, _) -> wo == WoWrite && v == var) $
                  sortOn (\(_, path, _, _, _) -> length path) targets
          in case relevantTarget of
               (x:_) -> Just x
               _ ->
                   case filter (\(v, _, _, _, pos) -> v == var && pos /= PIn) targets of
                     (x:_) -> Just x
                     _ -> Nothing
      relevantVars = S.fromList $ fmap a_value args
      handleTarget wt =
          case wt of
            WtMany x ->
                concatMap (handleTarget . WtPrim) x
            WtPrim (PwtVar x rks copyAllowed wo pos) ->
                if x `S.member` relevantVars then [(x, rks, copyAllowed, wo, pos)] else []
            WtPrim PwtNone -> []
