{-# LANGUAGE StrictData #-}
module Desugar.UniqueVars where

import Types.Ast
import Types.Common
import Types.Types

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
      _ -> error $ "runUniquify: Not implemented: " ++ show expr
