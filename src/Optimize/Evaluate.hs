module Optimize.Evaluate
    (evaluate)
where

import Analyse.VariableScopes
import Data.Maybe
import Types.Annotation
import Types.Ast

import Control.Monad.State
import Data.Functor.Identity
import qualified Data.HashMap.Strict as HM

import Data.Monoid
import Debug.Trace

evaluate :: Expr a -> Expr a
evaluate e =
    fst $ runIdentity $ runStateT (runExpr e) emptyState

data EvalState a
    = EvalState
    { es_scope :: HM.HashMap Var (InlineDecl, Expr a)
    } deriving (Show, Eq)

emptyState :: EvalState a
emptyState = EvalState mempty

scoped :: EvalM a m => StateT (EvalState a) m b -> m b
scoped go =
    do s <- get
       (a, _) <- runStateT go s
       pure a

data InlineDecl
    = InNever
    | InAlways
    | InTrivial
    deriving (Show, Eq)

declare :: EvalM a m => Var -> InlineDecl -> Expr a -> m ()
declare v idecl e =
    modify $ \es ->
    es
    { es_scope = HM.insert v (if isLambda e then InNever else idecl, e) (es_scope es)
    }

lookupVar :: EvalM a m => Var -> m (Maybe (InlineDecl, Expr a))
lookupVar v =
    do s <- get
       pure $ HM.lookup v (es_scope s)

type EvalM a = MonadState (EvalState a)

runList :: EvalM a m => a -> [Expr a] -> m (Expr a)
runList ann vals =
    EList . Annotated ann <$> mapM runExpr vals

runIf :: EvalM a m => a -> If a -> m (Expr a)
runIf ann rawIf =
    do evaledIf <- ifTransformM runExpr rawIf
       let ifBodies =
               filter (\(check, _) -> isBool False check) (if_bodies evaledIf)
       case ifBodies of
         ((cond, alwaysTaken):_) | isBool True cond -> pure alwaysTaken
         [] -> pure (if_else evaledIf)
         _ -> pure $ EIf $ Annotated ann $ If ifBodies (if_else evaledIf)

runLet :: EvalM a m => a -> Let a -> m (Expr a)
runLet ann (Let bv@(Annotated _ boundVar) boundExpr inExpr) =
    do let varOccurs =
               fromMaybe 0 $
               HM.lookup boundVar $ getFreeVarMap mempty inExpr
       case varOccurs of
         0 -> runExpr inExpr
         occs -> go (if occs == 1 then InAlways else InTrivial)
    where
        go idecl =
            do boundExpr' <-
                   scoped $
                   do declare boundVar idecl boundExpr
                      runExpr boundExpr
               finalIn <-
                   scoped $
                   do declare boundVar idecl boundExpr'
                      runExpr inExpr
               let finalOccurs = HM.lookup boundVar $ getFreeVarMap mempty finalIn
               case finalOccurs of
                 Nothing -> pure finalIn -- variable no longer needed
                 Just _ ->
                     pure $
                     ELet $ Annotated ann $ Let bv boundExpr' finalIn

runVar :: EvalM a m => a -> Var -> m (Expr a)
runVar ann var =
    do res <- lookupVar var
       case trace ("runVar: " <> show var <> " res:" <> show (fmap fst res)) res of
         Just (idecl, varE) ->
             case idecl of
               InAlways -> runExpr varE
               InTrivial ->
                   if isLiteral varE
                   then runExpr varE
                   else noInline
               InNever -> noInline
         Nothing -> noInline
    where
        noInline = pure (EVar $ Annotated ann var)

runLambda :: EvalM a m => a -> Lambda a -> m (Expr a)
runLambda ann (Lambda args body) =
    ELambda . Annotated ann <$> (Lambda args <$> runExpr body)

runBinOp :: forall a m. EvalM a m => a -> BinOp a -> m (Expr a)
runBinOp ann binOpRaw =
    do binOp <- binOpTransformM runExpr binOpRaw
       case binOp of
         BoAdd a b -> math binOp (+) a b
         BoSub a b -> math binOp (-) a b
         BoMul a b -> math binOp (*) a b
         BoDiv a b -> mathDbl binOp (/) a b
         BoEq a b -> cmp binOp (==) a b
         BoNeq a b -> cmp binOp (/=) a b
         BoGt a b -> cmp binOp (<) a b
         BoGtEq a b -> cmp binOp (<=) a b
         BoLt a b -> cmp binOp (>) a b
         BoLtEq a b -> cmp binOp (>=) a b
         BoNot a -> doNot binOp a
         BoAnd a b -> bool binOp (&&) a b
         BoOr a b -> bool binOp (||) a b
    where
        litRes l = pure $ ELit (Annotated ann l)
        noRun binOp = pure $ EBinOp (Annotated ann binOp)
        doNot binOp a =
            case toLiteral a of
              Just (LBool True) -> litRes $ LBool False
              Just (LBool False) -> litRes $ LBool True
              _ -> noRun binOp
        mathDbl ::
            BinOp a
            -> (Double -> Double -> Double) -> Expr a -> Expr a -> m (Expr a)
        mathDbl binOp f a b =
            case (,) <$> toLiteral a <*> toLiteral b of
              Just (LInt x, LInt y) ->
                  litRes $ LFloat (f (fromIntegral x) (fromIntegral y))
              Just (LFloat x, LFloat y) -> litRes $ LFloat (f x y)
              _ -> noRun binOp
        math ::
            BinOp a
            -> (forall x. Num x => x -> x -> x) -> Expr a -> Expr a -> m (Expr a)
        math binOp f a b =
            case (,) <$> toLiteral a <*> toLiteral b of
              Just (LInt x, LInt y) ->
                  litRes $ LInt (f x y)
              Just (LFloat x, LFloat y) -> litRes $ LFloat (f x y)
              _ -> noRun binOp
        cmp ::
            BinOp a
            -> (forall x. (Ord x, Eq x) => x -> x -> Bool) -> Expr a -> Expr a -> m (Expr a)
        cmp binOp f a b =
            -- This could potentially also do things with non bools
            case (,) <$> toLiteral a <*> toLiteral b of
              Just (LInt x, LInt y) -> litRes $ LBool (f x y)
              Just (LFloat x, LFloat y) -> litRes $ LBool (f x y)
              Just (LBool x, LBool y) -> litRes $ LBool (f x y)
              Just (LChar x, LChar y) -> litRes $ LBool (f x y)
              Just (LString x, LString y) -> litRes $ LBool (f x y)
              _ -> noRun binOp
        bool ::
            BinOp a
            -> (Bool -> Bool -> Bool) -> Expr a -> Expr a -> m (Expr a)
        bool binOp f a b =
            case (,) <$> toLiteral a <*> toLiteral b of
              Just (LBool x, LBool y) -> litRes $ LBool (f x y)
              _ -> noRun binOp

runExpr :: EvalM a m => Expr a -> m (Expr a)
runExpr expr =
    case expr of
      ELit _ -> pure expr -- can't really do anything
      EVar (Annotated x varE) -> runVar x varE
      EList (Annotated x listVals) -> runList x listVals
      EIf (Annotated x ifE) -> runIf x ifE
      ELet (Annotated x letE) -> runLet x letE
      EBinOp (Annotated x binOpE) -> runBinOp x binOpE
      ELambda (Annotated x lambdaE) -> runLambda x lambdaE
      _ ->
          trace ("Skipping!") $
          pure expr -- TODO: implement more evaluators :P
