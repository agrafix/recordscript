{-# LANGUAGE StrictData #-}
module Flow.CopyAnalysis where

import Types.Annotation
import Types.Ast
import Types.Common

import Data.List (foldl')
import Data.Monoid
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S

data PrimitiveWriteTarget
    = PwtVar Var [RecordKey]
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
    = FtFun [Maybe (Var, [RecordKey])]
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
      _ -> error ("OOPS: " ++ show expr)

funWriteThrough :: forall a. Show a => [Maybe (Var, [RecordKey])] -> [Expr a] -> FunInfo -> WriteTarget
funWriteThrough funType args funInfo =
    packMany $ fmap (uncurry makeTarget) $ zip funType args
    where
      makeTarget :: Maybe (Var, [RecordKey]) -> Expr a -> WriteTarget
      makeTarget mArgTy arg =
          case mArgTy of
            Nothing -> WtPrim PwtNone
            Just (_, keys) -> findWriteTarget arg keys funInfo

findWriteTarget :: forall a. Show a => Expr a -> [RecordKey] -> FunInfo -> WriteTarget
findWriteTarget expr pathTraversed funInfo =
    case expr of
      ELit _ -> WtPrim PwtNone -- ill typed
      EList _ -> WtPrim PwtNone -- ill typed
      EBinOp _ -> WtPrim PwtNone -- ill typed
      ELambda (Annotated _ (Lambda _ body)) ->
          -- TODO: is this correct? Probably need to remove the targets
          -- that the arguments already handle.
          findWriteTarget body pathTraversed funInfo
      ERecord _ -> WtPrim PwtNone -- don't care
      EVar (Annotated _ var) -> WtPrim (PwtVar var pathTraversed) -- trivial
      ERecordMerge (Annotated _ (RecordMerge tgt _ _)) ->
          findWriteTarget tgt pathTraversed funInfo
      ERecordAccess (Annotated _ (RecordAccess r rk)) ->
          findWriteTarget r (pathTraversed ++ [rk]) funInfo
      EIf (Annotated _ (If bodies elseExpr)) ->
          let exprs = fmap snd bodies ++ [elseExpr]
          in packMany $ fmap (\e -> findWriteTarget e pathTraversed funInfo) exprs
      ECase (Annotated _ (Case _ cases)) ->
          let exprs = fmap snd cases
          in packMany $ fmap (\e -> findWriteTarget e pathTraversed funInfo) exprs
      EFunApp (Annotated _ (FunApp rcvE args)) ->
          case getFunType rcvE funInfo of
            Nothing -> error ("Can't call function")
            Just FtSelf -> WtPrim PwtNone -- don't care about writes to self
            Just (FtFun ft) -> funWriteThrough ft args funInfo
            Just (FtRec r) -> error ("IMPLEMENT ME" ++ show r)
      ELet (Annotated _ (Let (Annotated _ var) bindE inE)) ->
          let tempFunInfo =
                  FunInfo $ HM.insert var FtSelf (unFunInfo funInfo)
              funInfo' =
                  case getFunType bindE tempFunInfo of
                    Nothing -> funInfo
                    Just fi -> FunInfo $ HM.insert var fi (unFunInfo funInfo)
              bindWt =
                  -- TODO: this seems incorrect.
                  findWriteTarget bindE pathTraversed funInfo'
              res =
                  handleLetTarget var bindE pathTraversed [] funInfo' $
                  findWriteTarget inE pathTraversed funInfo'
          in case res of
               WtPrim PwtNone -> bindWt
               _ -> res

handleLetTarget ::
    Show a => Var -> Expr a -> [RecordKey] -> [RecordKey] -> FunInfo -> WriteTarget -> WriteTarget
handleLetTarget var bindE pathTraversed pExtra funInfo wtarget =
    case wtarget of
      WtPrim (PwtVar v recordPath) | v == var ->
        case findWriteTarget bindE pathTraversed funInfo of
          WtPrim (PwtVar v2 rp2) ->
              WtPrim (PwtVar v2 (rp2 <> recordPath))
          WtMany wTargets ->
              packMany (fmap (handleLetTarget var bindE pathTraversed recordPath funInfo . WtPrim) wTargets)
          x -> x
      WtPrim (PwtVar v rp) -> WtPrim (PwtVar v (rp <> pExtra))
      WtPrim PwtNone -> WtPrim PwtNone
      WtMany wTargets ->
          packMany $ fmap (handleLetTarget var bindE pathTraversed pExtra funInfo . WtPrim) wTargets

-- | Given a lambda, infer which arguments
-- would need to be considered written if the result is written
argumentDependency :: Show a => FunInfo -> Lambda a -> [Maybe (Var, [RecordKey])]
argumentDependency funInfo (Lambda args body) =
    fmap (makeEntry . a_value) args
    where
      makeEntry var =
          case filter (\(v, _) -> v == var) targets of
            [x] -> Just x
            _ -> Nothing
      targets = handleTarget $ findWriteTarget body [] funInfo
      relevantVars = S.fromList $ fmap a_value args
      handleTarget wt =
          case wt of
            WtMany x ->
                concatMap (handleTarget . WtPrim) x
            WtPrim (PwtVar x rks) ->
                if x `S.member` relevantVars then [(x, rks)] else []
            WtPrim PwtNone -> []
