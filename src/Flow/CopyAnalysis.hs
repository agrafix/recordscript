{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Flow.CopyAnalysis where

import Types.Annotation
import Types.Ast
import Types.Common
import Types.CopyKinds

import Control.Monad.Except
import Control.Monad.State
import Data.Data
--import Data.List (foldl')
import Data.Monoid
import GHC.Generics
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HM
import qualified Data.Sequence as Seq
import qualified Data.Set as S

data CopyState
    = CoppyState
    { is_context :: Context
    , is_varSupply :: Int
    , is_cvarSupply :: Int
    } deriving (Show)

data Context
    = Context
    { ctx_varKinds :: HM.HashMap Var CopyKind
    , ctx_equivMap :: HM.HashMap CopyVar CopyKind
    } deriving (Show)

data Error
    = Error
    { e_pos :: TypedPos
    , e_error :: ErrorMessage
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

data ErrorMessage
    = EExpectedRecord CopyKind RecordKey
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

type CopyM m = (MonadError Error m, MonadState CopyState m)

data WriteTarget
    = WtVar Var
    | WtRecordKey Var [RecordKey]
    | WtMany [WriteTarget]
    | WtNone
    deriving (Show, Eq)

findWriteTarget :: Expr a -> [RecordKey] -> WriteTarget
findWriteTarget expr pathTraversed =
    case expr of
      ELit _ -> WtNone -- ill typed
      EList _ -> WtNone -- ill typed
      EBinOp _ -> WtNone -- ill typed
      ELambda _ -> WtNone -- ill typed
      ERecord _ -> WtNone -- don't care
      EVar (Annotated _ var) ->
          if null pathTraversed
          then WtVar var -- trivial
          else WtRecordKey var pathTraversed
      ERecordMerge (Annotated _ (RecordMerge tgt _ _)) ->
          findWriteTarget tgt pathTraversed
      ERecordAccess (Annotated _ (RecordAccess r rk)) ->
          findWriteTarget r (pathTraversed ++ [rk])
      EIf (Annotated _ (If bodies elseExpr)) ->
          let exprs = fmap snd bodies ++ [elseExpr]
          in WtMany $ fmap (flip findWriteTarget pathTraversed) exprs
      ECase (Annotated _ (Case _ cases)) ->
          let exprs = fmap snd cases
          in WtMany $ fmap (flip findWriteTarget pathTraversed) exprs
      EFunApp (Annotated _ (FunApp rcvE args)) ->
          -- TODO: this is tricky, here we need to know how the result
          -- related to it's arguments first.
          error "IMPLEMENT ME" rcvE args
      ELet (Annotated _ (Let (Annotated _ var) bindE inE)) ->
          -- TODO: This is probably only partially correct :sadpanda:
          case findWriteTarget inE pathTraversed of
            WtVar v | v == var ->
              findWriteTarget bindE pathTraversed
            WtRecordKey v recordPath | v == var ->
              case findWriteTarget bindE pathTraversed of
                WtVar v2
                    | null recordPath -> WtVar v2
                    | otherwise -> WtRecordKey v2 recordPath
                WtRecordKey v2 rp2 -> WtRecordKey v2 (rp2 <> recordPath)
                x -> x
            WtMany _ -> error "IMPLEMENT ME"
            x -> x

-- | Given a lambda, infer which arguments
-- would need to be considered written if the result is written
-- TODO: what about aliasing?
argumentDependency :: Lambda a -> [(Var, [RecordKey])]
argumentDependency (Lambda args body) =
    handleTarget $ findWriteTarget body []
    where
      relevantVars = S.fromList $ fmap a_value args
      handleTarget wt =
          case wt of
            WtNone -> []
            WtMany x ->
                concatMap handleTarget x
            WtVar x ->
                if x `S.member` relevantVars then [(x, [])] else []
            WtRecordKey x rks ->
                if x `S.member` relevantVars then [(x, rks)] else []

data Effect
    = EWritten Var
    | ERead Var
    | ESplit [Effect]
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

type EffectSeq = Seq.Seq Effect

effectSequence :: Expr TypedPos -> EffectSeq
effectSequence expr =
    case expr of
      ELit _ -> mempty
      EVar (Annotated _ var) -> pure (ERead var)
      EList (Annotated _ exprs) -> onSubSequence exprs
      ERecord (Annotated _ (Record hm)) ->
          -- TODO: is this correct? I think using a hash map is not optimal since
          -- the order in the map is different from how the fields appear in the
          -- source code.
          onSubSequence (HM.elems hm)
      ERecordAccess (Annotated _ (RecordAccess record _)) ->
          onSubSequence [record]
      ELet (Annotated _ (Let _ exprA exprB)) -> onSubSequence [exprA, exprB]
      EIf (Annotated _ (If bodies elseExpr)) ->
          let checks = fmap fst bodies
              runners = fmap snd bodies
              bodySplits = ESplit $ F.toList $ onSubSequence (runners ++ [elseExpr])
          in onSubSequence checks <> pure bodySplits
      ECase (Annotated _ (Case matchOn actions)) ->
          let bodySplits = ESplit $ F.toList $ onSubSequence $ fmap snd actions
          in onSubSequence [matchOn] <> pure bodySplits
      _ -> error "Not implemented"
    where
      onSubSequence exprs =
          join (Seq.fromList (map effectSequence exprs))

recordKeyKind :: CopyM m => TypedPos -> CopyKind -> RecordKey -> m CopyKind
recordKeyKind pos ck rk =
    case ck of
      CkRec _ (CopyRecordKind (Record record)) ->
          case HM.lookup rk record of
            Nothing -> badRecord
            Just v -> pure v
      _ -> badRecord
    where
      badRecord =
          throwError $ Error pos (EExpectedRecord ck rk)

-- | Record access is pretty trivial - since it's only a reading access
-- we'll simply pull the copy kind from the field
doRecordAccess :: CopyM m => TypedPos -> RecordAccess TypedPos -> m (Expr TypedPos, CopyKind)
doRecordAccess pos ra =
    do (targetRecord, recordKind) <- copyAnalysis (ra_record ra)
       copyKind <- recordKeyKind pos recordKind fld
       pure (ERecordAccess $ Annotated pos $ RecordAccess targetRecord fld, copyKind)
    where
        fld = ra_field ra

-- | A record construction is already tricky since we need to make sure that if a variable
-- is duplicated that we correctly insert a copy expression in the right place
-- TODO: this here is NOT implemented correctly as it stands :(
doRecord :: CopyM m => TypedPos -> Record (Expr TypedPos) -> m (Expr TypedPos, CopyKind)
doRecord pos (Record hm) =
    do kvKinds <-
           forM (HM.toList hm) $ \(rKey, rExpr) ->
           do (expr, exprKind) <- copyAnalysis rExpr
              pure (rKey, expr, exprKind)
       let copyKind =
               HM.fromList $ map (\(rKey, _, exprKind) -> (rKey, exprKind)) kvKinds
           recBody =
               HM.fromList $ map (\(rKey, expr, _) -> (rKey, expr)) kvKinds
       pure
           ( ERecord (Annotated pos (Record recBody))
           , CkRec CrDontCare $ CopyRecordKind $ Record copyKind
           )

copyAnalysis :: CopyM m => Expr TypedPos -> m (Expr TypedPos, CopyKind)
copyAnalysis expr =
    case expr of
      ELit _ -> pure (expr, CkExplicit CrDontCare)
      ERecordAccess (Annotated pos recordAccess) -> doRecordAccess pos recordAccess
      ERecord (Annotated pos record) -> doRecord pos record
      _ -> undefined
