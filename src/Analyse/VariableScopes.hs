module Analyse.VariableScopes
    (getFreeVars, getFreeVarMap, patternVars)
where

import Types.Annotation
import Types.Ast
import Types.Common

import Control.Monad
import Control.Monad.State
import Data.Functor.Identity
import Data.Set (Set)
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S

getFreeVars :: Set Var -> Expr a -> Set Var
getFreeVars seen e =
    S.fromList $ HM.keys $ getFreeVarMap seen e

getFreeVarMap :: Set Var -> Expr a -> HM.HashMap Var Int
getFreeVarMap seen e =
    vs_free $ snd $ runIdentity $
    runStateT (collectFreeVariables e) (VarSet seen mempty)

data VarSet
    = VarSet
    { vs_seen :: Set Var
    , vs_free :: HM.HashMap Var Int
    } deriving (Show, Eq)

type CollectM = MonadState VarSet

scoped :: CollectM m => StateT VarSet m a -> m a
scoped go =
    do s <- get
       (a, s') <- runStateT go s
       put $ s { vs_free = vs_free s' }
       pure a

markAsFree :: CollectM m => Var -> m ()
markAsFree v =
    modify $ \vs -> vs { vs_free = HM.insertWith (+) v 1 (vs_free vs) }

markAsSeen :: CollectM m => Var -> m ()
markAsSeen v =
    modify $ \vs -> vs { vs_seen = S.insert v (vs_seen vs) }

hasSeen :: CollectM m => Var -> m Bool
hasSeen x =
    do seen <- vs_seen <$> get
       pure (S.member x seen)

patternVars :: Pattern a -> [Var]
patternVars p =
    case p of
      PVar (Annotated _ v) -> [v]
      PLit _ -> []
      PRecord (Annotated _ (Record hm)) ->
          concatMap patternVars (HM.elems hm)
      PAny _ -> []

collectCase :: CollectM m => Case a -> m ()
collectCase (Case matchOn cases) =
    do collectFreeVariables matchOn
       forM_ cases $ \(pat, expr) ->
           scoped $
           do mapM_ markAsSeen (patternVars pat)
              collectFreeVariables expr

collectLambda :: CollectM m => Lambda a -> m ()
collectLambda (Lambda args body) =
    scoped $
    do forM_ args $ \(Annotated _ var) -> markAsSeen var
       collectFreeVariables body

collectLet :: CollectM m => Let a -> m ()
collectLet (Let (Annotated _ var) boundExpr inExpr) =
    scoped $
    do markAsSeen var
       collectFreeVariables boundExpr
       collectFreeVariables inExpr

collectFreeVariables :: CollectM m => Expr a -> m ()
collectFreeVariables expr =
    case expr of
      ELit _ -> pure ()
      EVar (Annotated _ var) ->
          do didSee <- hasSeen var
             unless didSee $ markAsFree var
      EList (Annotated _ listVals) -> mapM_ collectFreeVariables listVals
      ERecord (Annotated _ r) ->
          void $ recordMapMaybeM (fmap Just . collectFreeVariables) r
      ERecordMerge (Annotated _ rm) -> void $ recordMergeApplyM collectFreeVariables rm
      ERecordAccess (Annotated _ ra) ->
          void $ recordAccessApplyM collectFreeVariables ra
      EIf (Annotated _ ifCond) -> void $ ifApplyM collectFreeVariables ifCond
      EFunApp (Annotated _ funAppE) -> funAppApplyM collectFreeVariables funAppE
      EBinOp (Annotated _ bo) -> binOpApplyM collectFreeVariables bo
      ECopy e -> collectFreeVariables e
      ECase (Annotated _ caseE) -> collectCase caseE
      ELet (Annotated _ letE) -> collectLet letE
      ELambda (Annotated _ lambdaE) -> collectLambda lambdaE
