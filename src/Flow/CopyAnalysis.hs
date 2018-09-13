{-# LANGUAGE StrictData #-}
module Flow.CopyAnalysis
    ( writePathAnalysis
    , emptyEnv, emptyFunInfo
    , WriteTarget(..), PrimitiveWriteTarget(..)
    , CopyAllowed(..), WriteOccured(..)
    , argumentDependency
    )
where

import Types.Annotation
import Types.Ast
import Types.Common

import Data.List (foldl')
import Data.Monoid
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S

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

getFunType :: (AnalysisM m, Show a) => Expr a -> FunInfo -> m (Maybe FunType)
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
    forall m a. (AnalysisM m, Show a)
    => [Maybe (Var, [RecordKey], CopyAllowed, WriteOccured)]
    -> [Expr a]
    -> FunInfo
    -> m WriteTarget
funWriteThrough funType args funInfo =
    packMany <$> mapM (uncurry makeTarget) (zip funType args)
    where
      makeTarget ::
          Maybe (Var, [RecordKey], CopyAllowed, WriteOccured)
          -> Expr a
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

-- For now, just monadic. But error handling will
-- follow
type AnalysisM m = Monad m

writePathAnalysis :: forall a m. (AnalysisM m, Show a) => Expr a -> Env -> m WriteTarget
writePathAnalysis expr env =
    case expr of
      ELit _ -> pure $ WtPrim PwtNone -- ill typed
      EList _ -> pure $ WtPrim PwtNone -- ill typed
      EBinOp _ -> pure $ WtPrim PwtNone -- ill typed
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
    (AnalysisM m, Show a)
    => Var -> Expr a -> [RecordKey] -> [RecordKey] -> FunInfo -> WriteTarget -> m WriteTarget
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
    (AnalysisM m, Show a)
    => FunInfo
    -> Lambda a
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
