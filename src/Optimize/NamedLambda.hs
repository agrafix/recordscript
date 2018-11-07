module Optimize.NamedLambda
    ( nameLambdas, runNamedLambda )
where

import Types.Annotation
import Types.Ast
import Types.Common
import Util.NameMonad

runNamedLambda :: NameMonad a -> a
runNamedLambda = runNameM "lambda"

handleLet :: (Show a, NameM m) => Let a -> m (Let a)
handleLet (Let boundVar boundExpr inExpr) =
    do boundExpr' <-
           case boundExpr of
             ELambda (Annotated x (Lambda args body)) ->
                 do body' <- nameLambdas body
                    pure $ ELambda $ Annotated x (Lambda args body')
             _ -> nameLambdas boundExpr
       inExpr' <- nameLambdas inExpr
       pure $ Let boundVar boundExpr' inExpr'

handleLambda :: (Show a, NameM m) => a -> Lambda a -> m (Expr a)
handleLambda ann (Lambda args body) =
    do var <- freshVar
       body' <- nameLambdas body
       pure $
           ELet $ Annotated ann $
           Let
           { l_boundVar = Annotated ann var
           , l_boundExpr = ELambda $ Annotated ann (Lambda args body')
           , l_in = EVar (Annotated ann var)
           }

nameLambdas :: (Show a, NameM m) => Expr a -> m (Expr a)
nameLambdas expr =
    case expr of
      ELit _ -> pure expr
      EVar _ -> pure expr
      EList (Annotated x listVals) ->
          EList . Annotated x <$> mapM nameLambdas listVals
      ERecord (Annotated x r) ->
          ERecord . Annotated x <$> recordMapMaybeM (fmap Just . nameLambdas) r
      ERecordMerge (Annotated x rm) ->
          ERecordMerge . Annotated x <$> recordMergeTransformM nameLambdas rm
      ERecordAccess (Annotated x ra) ->
          ERecordAccess . Annotated x <$> recordAccessTransformM nameLambdas ra
      EIf (Annotated x ifCond) ->
          EIf . Annotated x <$> ifTransformM nameLambdas ifCond
      ELet (Annotated x letE) ->
          ELet . Annotated x <$> handleLet letE
      ELambda (Annotated x lambda) ->
          handleLambda x lambda
      EFunApp (Annotated x funAppE) ->
          EFunApp . Annotated x <$> funAppTransformM nameLambdas funAppE
      ECase (Annotated x caseE) ->
          ECase . Annotated x <$> caseTransformM nameLambdas caseE
      EBinOp (Annotated x bo) ->
          EBinOp . Annotated x <$> binOpTransformM nameLambdas bo
      ECopy e -> ECopy <$> nameLambdas e
