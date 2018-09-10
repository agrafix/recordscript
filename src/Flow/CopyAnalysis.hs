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

getFunType :: Show a => Expr a -> FunInfo -> Maybe FunType
getFunType expr funInfo =
    case expr of
      ELambda (Annotated _ lambda) -> Just $ FtFun $ argumentDependency funInfo lambda
      EVar (Annotated _ var) -> HM.lookup var (unFunInfo funInfo)
      ERecordAccess (Annotated _ (RecordAccess r rk)) ->
          case getFunType r funInfo of
            Nothing -> Nothing
            Just ft -> pathLookup [rk] ft
      ERecord (Annotated _ record) ->
          Just $ FtRec $ recordMapMaybe (\e -> getFunType e funInfo) record
      EFunApp (Annotated _ (FunApp rcvE _)) ->
          getFunType rcvE funInfo
      _ -> Nothing -- is this right??

funWriteThrough ::
    forall a. Show a
    => [Maybe (Var, [RecordKey], CopyAllowed, WriteOccured)]
    -> [Expr a]
    -> FunInfo
    -> WriteTarget
funWriteThrough funType args funInfo =
    packMany $ fmap (uncurry makeTarget) $ zip funType args
    where
      makeTarget ::
          Maybe (Var, [RecordKey], CopyAllowed, WriteOccured)
          -> Expr a
          -> WriteTarget
      makeTarget mArgTy arg =
          case mArgTy of
            Nothing ->
                WtPrim PwtNone
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

writePathAnalysis :: forall a. Show a => Expr a -> Env -> WriteTarget
writePathAnalysis expr env =
    case expr of
      ELit _ -> WtPrim PwtNone -- ill typed
      EList _ -> WtPrim PwtNone -- ill typed
      EBinOp _ -> WtPrim PwtNone -- ill typed
      ELambda (Annotated _ (Lambda _ body)) ->
          -- TODO: is this correct? Probably need to remove the targets
          -- that the arguments already handle.
          writePathAnalysis body env
      ERecord _ -> WtPrim PwtNone -- don't care
      EVar (Annotated _ var) ->
          WtPrim (PwtVar var (e_pathTraversed env) (e_copyAllowed env) (e_writeOccured env))
      ERecordMerge (Annotated _ (RecordMerge tgt _ noCopy)) ->
          writePathAnalysis tgt $
          env
          { e_copyAllowed = if not noCopy then CaAllowed else CaBanned
          , e_writeOccured = WoWrite
          }
      ERecordAccess (Annotated _ (RecordAccess r rk)) ->
          writePathAnalysis r $ env { e_pathTraversed = e_pathTraversed env ++ [rk] }
      EIf (Annotated _ (If bodies elseExpr)) ->
          let exprs = fmap snd bodies ++ [elseExpr]
          in packMany $ fmap (\e -> writePathAnalysis e env) exprs
      ECase (Annotated _ (Case _ cases)) ->
          let exprs = fmap snd cases
          in packMany $ fmap (\e -> writePathAnalysis e env) exprs
      EFunApp (Annotated _ (FunApp rcvE args)) ->
          case getFunType rcvE (e_funInfo env) of
            Nothing -> error ("Can't call function")
            Just FtSelf -> WtPrim PwtNone -- don't care about writes to self
            Just (FtFun ft) -> funWriteThrough ft args (e_funInfo env)
            Just (FtRec r) -> error ("IMPLEMENT ME" ++ show r)
      ELet (Annotated _ (Let (Annotated _ var) bindE inE)) ->
          let tempFunInfo =
                  FunInfo $ HM.insert var FtSelf (unFunInfo $ e_funInfo env)
              funInfo' =
                  case getFunType bindE tempFunInfo of
                    Nothing -> e_funInfo env
                    Just fi -> FunInfo $ HM.insert var fi (unFunInfo $ e_funInfo env)
              bindWt =
                  -- TODO: this seems incorrect.
                  writePathAnalysis bindE $ env { e_funInfo = funInfo' }
              res =
                  handleLetTarget var bindE (e_pathTraversed env) [] funInfo' $
                  writePathAnalysis inE $ env { e_funInfo = funInfo' }
          in case res of
               WtPrim PwtNone -> bindWt
               _ -> res

handleLetTarget ::
    Show a => Var -> Expr a -> [RecordKey] -> [RecordKey] -> FunInfo -> WriteTarget -> WriteTarget
handleLetTarget var bindE pathTraversed pExtra funInfo wtarget =
    case wtarget of
      WtPrim (PwtVar v recordPath ca wo) | v == var ->
        case writePathAnalysis bindE (Env pathTraversed funInfo ca wo) of
          WtPrim (PwtVar v2 rp2 ca2 wo2) ->
              WtPrim (PwtVar v2 (rp2 <> recordPath) ca2 wo2)
          WtMany wTargets ->
              packMany (fmap (handleLetTarget var bindE pathTraversed recordPath funInfo . WtPrim) wTargets)
          z -> z
      WtPrim (PwtVar v rp x y) -> WtPrim (PwtVar v (rp <> pExtra) x y)
      WtPrim PwtNone -> WtPrim PwtNone
      WtMany wTargets ->
          packMany $ fmap (handleLetTarget var bindE pathTraversed pExtra funInfo . WtPrim) wTargets

-- | Given a lambda, infer which arguments
-- would need to be considered written if the result is written
argumentDependency ::
    Show a
    => FunInfo
    -> Lambda a
    -> [Maybe (Var, [RecordKey], CopyAllowed, WriteOccured)]
argumentDependency funInfo (Lambda args body) =
    fmap (makeEntry . a_value) args
    where
      makeEntry var =
          case filter (\(v, _, _, _) -> v == var) targets of
            [x] -> Just x
            _ -> Nothing
      targets =
          handleTarget $ writePathAnalysis body (Env [] funInfo CaAllowed WoRead)
      relevantVars = S.fromList $ fmap a_value args
      handleTarget wt =
          case wt of
            WtMany x ->
                concatMap (handleTarget . WtPrim) x
            WtPrim (PwtVar x rks copyAllowed wo) ->
                if x `S.member` relevantVars then [(x, rks, copyAllowed, wo)] else []
            WtPrim PwtNone -> []
