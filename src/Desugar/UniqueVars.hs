{-# LANGUAGE StrictData #-}
module Desugar.UniqueVars where

import Types.Ast
import Types.Common

import Control.Monad
import Control.Monad.State
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T

data UniqueState
    = UniqueState
    { us_varSupply :: Int
    , us_replaceMap :: HM.HashMap Var Var
    }
    deriving (Show, Eq)

type UniqueM m = (MonadState UniqueState m)


scoped :: UniqueM m => StateT UniqueState m a -> m a
scoped go =
    do s <- get
       (a, s') <- runStateT go s
       put $ s { us_varSupply = us_varSupply s' }
       pure a

uniquify :: UniqueM m => Var -> m Var
uniquify q@(Var x) =
    do s <- get
       case HM.lookup q (us_replaceMap s) of
         Just y -> pure y
         Nothing ->
             do let idx = us_varSupply s
                    v' = Var $ T.pack $ T.unpack x ++ "@@" ++ show idx
                put $
                    s
                    { us_varSupply = us_varSupply s + 1
                    , us_replaceMap = HM.insert q v' (us_replaceMap s)
                    }
                pure v'

runUniquifyPat :: (Show a, UniqueM m) => Pattern a -> m (Pattern a)
runUniquifyPat p =
    case p of
      PLit _ -> pure p
      PAny _ -> pure p
      PVar v -> PVar <$> mapMA uniquify v
      PRecord r ->
          fmap PRecord $ flip mapMA r $ \(Record hm) ->
          fmap (Record . HM.fromList) $ forM (HM.toList hm) $ \(lbl, pat) ->
          (,) <$> pure lbl <*> runUniquifyPat pat

-- todo: can we do scope checking here too?
runUniquify :: (Show a, UniqueM m) => Expr a -> m (Expr a)
runUniquify expr =
    case expr of
      ELit _ -> pure expr
      EVar v -> EVar <$> mapMA uniquify v
      EList l ->
          fmap EList $
          flip mapMA l $ \exprList ->
          mapM runUniquify exprList
      ERecord r ->
          fmap ERecord $
          flip mapMA r $ \recVal ->
          mapM runUniquify recVal
      ERecordMerge r ->
          fmap ERecordMerge $
          flip mapMA r $ \recMerge ->
          RecordMerge <$> runUniquify (rm_target recMerge) <*> mapM runUniquify (rm_mergeIn recMerge)
      EIf i ->
          fmap EIf $ flip mapMA i $ \iVal ->
          do bodies <-
                 forM (if_bodies iVal) $ \(x, y) ->
                 (,) <$> runUniquify x <*> runUniquify y
             If bodies <$> runUniquify (if_else iVal)
      ELet l ->
          fmap ELet $ flip mapMA l $ \letVal ->
          scoped $
          do var <- mapMA uniquify (l_boundVar letVal)
             boundE <- runUniquify (l_boundExpr letVal)
             inE <- runUniquify (l_in letVal)
             pure $ Let var boundE inE
      ELambda l ->
          fmap ELambda $ flip mapMA l $ \lambdaVal ->
          scoped $
          do vars <- mapM (mapMA uniquify) (l_args lambdaVal)
             bodyE <- runUniquify (l_body lambdaVal)
             pure $ Lambda vars bodyE
      EFunApp f ->
          fmap EFunApp $ flip mapMA f $ \funApp ->
          do recv <- runUniquify (fa_receiver funApp)
             args <- mapM runUniquify (fa_args funApp)
             pure $ FunApp recv args
      ECase c ->
          fmap ECase $ flip mapMA c $ \caseExpr ->
          do matchOn <- runUniquify (c_matchOn caseExpr)
             cases <-
                 forM (c_cases caseExpr) $ \(pat, patExpr) ->
                 scoped $
                 do pat' <- runUniquifyPat pat
                    expr' <- runUniquify patExpr
                    pure (pat', expr')
             pure $ Case matchOn cases
