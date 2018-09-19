{-# LANGUAGE StrictData #-}
module Flow.CopyAnalysis
    ( writePathAnalysis
    , emptyEnv, emptyFunInfo
    , WriteTarget(..), PrimitiveWriteTarget(..)
    , CopyAllowed(..), WriteOccured(..)
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
import Data.List (foldl', sortOn)
import Data.Maybe
import Data.Monoid
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S
import qualified Data.Text as T

data Error
    = Error
    { e_pos :: Pos
    , e_error :: ErrorMessage
    } deriving (Eq, Ord, Show)

prettyCopyError :: Error -> T.Text
prettyCopyError e =
    "Error on " <> T.pack (show $ e_pos e) <> ": \n"
    <> prettyErrorMessage (e_error e)

data ErrorMessage
    = ECantCopy Var [RecordKey]
    deriving (Eq, Ord, Show)

prettyErrorMessage :: ErrorMessage -> T.Text
prettyErrorMessage em =
    case em of
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
       pure $ Var $ T.pack $ "internal" ++ (show $ as_varSupply s)

type AnalysisM m = (MonadError Error m, MonadState AnalysisState m)
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

data PrimitiveWriteTarget
    = PwtVar Var [RecordKey] CopyAllowed WriteOccured
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

applyCopyActions :: AnalysisM m => [CopyAction] -> Expr TypedPos -> Expr TypedPos -> m (Expr TypedPos, Expr TypedPos)
applyCopyActions cas lhs rhs =
    loop cas lhs rhs
    where
      loop actions l r =
          case actions of
            [] -> pure (l, r)
            (ca:more) ->
                do (l', r') <- applyCopyAction ca l r
                   loop more l' r'

applyCopyAction :: AnalysisM m => CopyAction -> Expr TypedPos -> Expr TypedPos -> m (Expr TypedPos, Expr TypedPos)
applyCopyAction ca lhs rhs =
    case ca_side ca of
      CsLeft ->
          do lhs' <- applySingleCopyAction ca lhs
             pure (lhs', rhs)
      CsRight ->
          do rhs' <- applySingleCopyAction ca rhs
             pure (lhs, rhs')

applySingleCopyAction :: AnalysisM m => CopyAction -> Expr TypedPos -> m (Expr TypedPos)
applySingleCopyAction ca expr =
    do bindVar <- freshVar
       let exprAnn = getExprAnn expr
           pos = tp_pos exprAnn
           ann = TypedPos pos (TVar (TypeVar "<unknown>"))
           boundVar =
               Annotated ann bindVar
           boundExpr =
               ECopy $ makeAccessExpr pos ca
       pure $
           ELet $ Annotated exprAnn $
           Let boundVar boundExpr expr -- TODO actually use the introduced copy

joinWritePaths :: AnalysisM m => Pos -> WriteTarget -> WriteTarget -> m (WriteTarget, [CopyAction])
joinWritePaths pos w1 w2 =
    case (w1, w2) of
      (WtPrim PwtNone, x) -> pure (x, mempty)
      (x, WtPrim PwtNone) -> pure (x, mempty)
      (WtPrim x, WtPrim y) -> first (packMany . map WtPrim) <$> handleTargets pos [x] [y]
      (WtPrim x, WtMany y) -> first (packMany . map WtPrim) <$> handleTargets pos [x] y
      (WtMany x, WtPrim y) -> first (packMany . map WtPrim) <$> handleTargets pos x [y]
      (WtMany x, WtMany y) -> first (packMany . map WtPrim) <$> handleTargets pos x y

type TargetTuple = (Var, [RecordKey], CopyAllowed, WriteOccured)

shortestVarPath :: [TargetTuple] -> Maybe TargetTuple
shortestVarPath tts =
    case sortOn (\(_, rks, _, _) -> length rks) tts of
      [] -> Nothing
      (t : _) -> Just t

copyActionGen :: Bool -> [TargetTuple] -> CopySide -> Maybe CopyAction
copyActionGen needsWrite tts cs =
    fmap mkCopy $ propagationVal needsWrite tts
    where
      mkCopy (v, rks, _, _) =
          CopyAction v rks cs

propagationVal :: Bool -> [TargetTuple] -> Maybe TargetTuple
propagationVal needsWrite tts =
    shortestVarPath $ if needsWrite then filter writes tts else tts

writes :: TargetTuple -> Bool
writes (_, _, _, wo) = wo == WoWrite

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
                 PwtVar x rk ca wo -> HM.insertWith (++) x [(x, rk, ca, wo)] hm
           makeByVar = foldl' folder mempty
           byVar =
               let l = HM.map (\x -> (x, mempty)) $ makeByVar lhs
                   r = HM.map (\x -> (mempty, x)) $ makeByVar rhs
               in HM.elems $ HM.unionWith (\(a, b) (x, y) -> (a ++ x, b ++ y)) l r
           repack (x, rk, ca, wo) = PwtVar x rk ca wo
           allowsCopy (_, _, ca, _) = ca == CaAllowed
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
                                  (var, rks, _, _) =
                                      fromJust $
                                      propagationVal True (l ++ r)
                              case (canCopyL, canCopyR) of
                                (False, False) ->
                                    throwError $ Error pos $ ECantCopy var rks
                                (True, _) ->
                                    pure
                                        ( writeTargets ++ maybeToList (propagationVal writesR r)
                                        , copyActions ++ maybeToList (copyActionGen writesL l CsLeft)
                                        )
                                (_, True) ->
                                    pure
                                        ( writeTargets ++ maybeToList (propagationVal writesL l)
                                        , copyActions ++ maybeToList (copyActionGen writesR r CsRight)
                                        )

       first (map repack) <$> foldM handlePair (mempty, mempty) byVar

hadWrite :: WriteTarget -> Bool
hadWrite wt =
    case wt of
      WtPrim pwt -> handlePwt pwt
      WtMany wmany -> any handlePwt wmany
    where
      handlePwt p =
          case p of
            PwtNone -> False
            PwtVar _ _ _ WoWrite -> True
            _ -> False

packMany :: [WriteTarget] -> WriteTarget
packMany wts =
    case wts of
      [] -> WtMany []
      [x] -> x
      many ->
          let merged = foldl' merge mempty many
          in case merged of
              [x] -> WtPrim x
              xs -> WtMany xs
    where
      merge accum wtgt =
          case wtgt of
            WtPrim PwtNone -> accum
            WtPrim pwt -> accum <> [pwt]
            WtMany pwts -> accum <> pwts

data FunType
    = FtFun [Maybe (Var, [RecordKey], CopyAllowed, WriteOccured)]
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
    => [Maybe (Var, [RecordKey], CopyAllowed, WriteOccured)]
    -> [Expr TypedPos]
    -> FunInfo
    -> m WriteTarget
funWriteThrough funType args funInfo =
    packMany <$> mapM (uncurry makeTarget) (zip funType args)
    where
      makeTarget ::
          Maybe (Var, [RecordKey], CopyAllowed, WriteOccured)
          -> Expr TypedPos
          -> m WriteTarget
      makeTarget mArgTy arg =
          case mArgTy of
            Nothing ->
                pure $ WtPrim PwtNone
            Just (_, keys, copyAllowed, wo) ->
                writePathAnalysis arg (Env keys funInfo copyAllowed wo)

data Env
    = Env
    { e_pathTraversed :: [RecordKey]
    , e_funInfo :: FunInfo
    , e_copyAllowed :: CopyAllowed
    , e_writeOccured :: WriteOccured
    } deriving (Show, Eq)

emptyEnv :: Env
emptyEnv = Env [] emptyFunInfo CaAllowed WoRead

handleBinOp :: AnalysisM m => Env -> TypedPos -> BinOp TypedPos -> m (WriteTarget, BinOp TypedPos)
handleBinOp env (TypedPos pos _) bo =
    case bo of
      BoAdd x y ->
          do lhs <- writePathAnalysis x env
             rhs <- writePathAnalysis y env
             (writeTarget, copyActions) <- joinWritePaths pos lhs rhs
             (l, r) <- applyCopyActions copyActions x y
             pure (writeTarget, BoAdd l r)
      _ -> error "Undefined" -- TODO

writePathAnalysis :: forall m. AnalysisM m => Expr TypedPos -> Env -> m WriteTarget
writePathAnalysis expr env =
    case expr of
      ECopy _ -> pure $ WtPrim PwtNone -- should never happen
      ELit _ -> pure $ WtPrim PwtNone -- ill typed
      EList _ -> pure $ WtPrim PwtNone -- ill typed
      EBinOp (Annotated pos bo) ->
          fst <$> handleBinOp env pos bo -- TODO
      ELambda (Annotated _ (Lambda _ body)) ->
          -- TODO: is this correct? Probably need to remove the targets
          -- that the arguments already handle.
          writePathAnalysis body env
      ERecord _ -> pure $ WtPrim PwtNone -- don't care
      EVar (Annotated _ var) ->
          pure $ WtPrim (PwtVar var (e_pathTraversed env) (e_copyAllowed env) (e_writeOccured env))
      ERecordMerge (Annotated _ (RecordMerge tgt _ noCopy)) ->
          writePathAnalysis tgt $
          env
          { e_copyAllowed = if not noCopy then CaAllowed else CaBanned
          , e_writeOccured = WoWrite
          }
      ERecordAccess (Annotated _ (RecordAccess r rk)) ->
          writePathAnalysis r $ env { e_pathTraversed = e_pathTraversed env ++ [rk] }
      EIf (Annotated _ (If bodies elseExpr)) ->
          do let exprs = fmap snd bodies ++ [elseExpr]
             packMany <$> mapM (\e -> writePathAnalysis e env) exprs
      ECase (Annotated _ (Case _ cases)) ->
          do let exprs = fmap snd cases
             packMany <$> mapM (\e -> writePathAnalysis e env) exprs
      EFunApp (Annotated _ (FunApp rcvE args)) ->
          getFunType rcvE (e_funInfo env) >>= \funType ->
          case funType of
            Nothing -> error "Can't call function"
            Just FtSelf -> pure $ WtPrim PwtNone -- don't care about writes to self
            Just (FtFun ft) -> funWriteThrough ft args (e_funInfo env)
            Just (FtRec r) -> error ("IMPLEMENT ME" ++ show r)
      ELet (Annotated _ (Let (Annotated _ var) bindE inE)) ->
          do let tempFunInfo =
                     FunInfo $ HM.insert var FtSelf (unFunInfo $ e_funInfo env)
             funInfo' <-
                 getFunType bindE tempFunInfo >>= \funType ->
                 case funType of
                   Nothing -> pure $ e_funInfo env
                   Just fi -> pure $ FunInfo $ HM.insert var fi (unFunInfo $ e_funInfo env)
             bindWt <-
                 -- TODO: this seems incorrect.
                 writePathAnalysis bindE $ env { e_funInfo = funInfo' }
             res <-
                 do inRes <- writePathAnalysis inE $ env { e_funInfo = funInfo' }
                    handleLetTarget var bindE (e_pathTraversed env) [] funInfo' inRes
             pure $ case res of
               WtPrim PwtNone -> bindWt
               _ | not (hadWrite res) && hadWrite bindWt -> bindWt
               _ -> res

handleLetTarget ::
    AnalysisM m
    => Var -> Expr TypedPos -> [RecordKey] -> [RecordKey] -> FunInfo -> WriteTarget -> m WriteTarget
handleLetTarget var bindE pathTraversed pExtra funInfo wtarget =
    case wtarget of
      WtPrim (PwtVar v recordPath ca wo) | v == var ->
        writePathAnalysis bindE (Env pathTraversed funInfo ca wo) >>= \wpRes ->
        case wpRes of
          WtPrim (PwtVar v2 rp2 ca2 wo2) ->
              pure $ WtPrim (PwtVar v2 (rp2 <> recordPath) ca2 wo2)
          WtMany wTargets ->
              packMany <$> mapM (handleLetTarget var bindE pathTraversed recordPath funInfo . WtPrim) wTargets
          z -> pure z
      WtPrim (PwtVar v rp x y) ->
          pure $ WtPrim (PwtVar v (rp <> pExtra) x y)
      WtPrim PwtNone ->
          pure $ WtPrim PwtNone
      WtMany wTargets ->
          packMany <$> mapM (handleLetTarget var bindE pathTraversed pExtra funInfo . WtPrim) wTargets

-- | Given a lambda, infer which arguments
-- would need to be considered written if the result is written
argumentDependency ::
    AnalysisM m
    => FunInfo
    -> Lambda TypedPos
    -> m [Maybe (Var, [RecordKey], CopyAllowed, WriteOccured)]
argumentDependency funInfo (Lambda args body) =
    do targets <-
           handleTarget <$> writePathAnalysis body (Env [] funInfo CaAllowed WoRead)
       pure $ fmap (makeEntry targets . a_value) args
    where
      makeEntry targets var =
          case filter (\(v, _, _, _) -> v == var) targets of
            [x] -> Just x
            _ -> Nothing
      relevantVars = S.fromList $ fmap a_value args
      handleTarget wt =
          case wt of
            WtMany x ->
                concatMap (handleTarget . WtPrim) x
            WtPrim (PwtVar x rks copyAllowed wo) ->
                if x `S.member` relevantVars then [(x, rks, copyAllowed, wo)] else []
            WtPrim PwtNone -> []
