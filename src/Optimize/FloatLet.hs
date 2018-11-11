module Optimize.FloatLet
    ( floater )
where

import Types.Annotation
import Types.Ast
import Types.Common

import Control.Monad
import Control.Monad.State
import Data.Functor.Identity
import Data.List (foldl')
import Data.Monoid
import Data.Set (Set)
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S
import qualified Data.SortedList as SL

import Debug.Trace

data OpenLetEntry a
    = OpenLetEntry
    { ol_close :: Expr a -> Expr a
    , ol_bind :: Set Var
    , ol_free :: Set Var
    }

instance Show (OpenLetEntry a) where
    show ole =
        "OpenLetEntry { ol_close = undefined, ol_bind = "
        <> show (ol_bind ole) <> ", ol_free = " <> show (ol_free ole) <> "}"

instance Eq (OpenLetEntry a) where
    (/=) ol1 ol2 =
        not (S.null (ol_bind ol1 `S.intersection` ol_free ol2))

instance Ord (OpenLetEntry a) where
    (<=) ol1 ol2 =
        not (S.null (ol_bind ol1 `S.intersection` ol_free ol2))

data OpenLet a
    = OpenLet
    { ol_stack :: SL.SortedList (OpenLetEntry a)
    } deriving (Show)

emptyOpenLet :: OpenLet a
emptyOpenLet = OpenLet mempty

combineOpenLet :: OpenLet a -> OpenLet a -> OpenLet a
combineOpenLet ol1 ol2 =
    OpenLet
    { ol_stack = ol_stack ol1 <> ol_stack ol2
    }

data SplitResult a
    = SplitResult
    { sr_pass :: OpenLet a
      -- ^ safe to pass beyond the variable binding
    , sr_apply :: OpenLet a
      -- ^ apply at current level
    }

splitOpenLet :: S.Set Var -> OpenLet a -> SplitResult a
splitOpenLet boundVars openLet =
    let applySpan ole =
            S.null (boundVars `S.intersection` ol_free ole)
        (pass, apply) =
            span applySpan $ reverse $ F.toList (ol_stack openLet)
    in trace ("Split: pass=" <> show pass <> " apply=" <> show apply) $
       SplitResult
       { sr_pass = OpenLet $ SL.toSortedList pass
       , sr_apply = OpenLet $ SL.toSortedList apply
       }

instance Monoid (OpenLet a) where
    mempty = emptyOpenLet
    mappend = combineOpenLet

toOpenLet :: Monad m => a -> Let a -> m (OpenLet a, Expr a)
toOpenLet a (Let boundVar@(Annotated _ v) boundExpr inVal) =
    do (boundOlRaw, boundExprRaw) <- floatLet boundExpr
       let split = splitOpenLet (S.singleton v) boundOlRaw
           boundExpr' = applyOpenLet (sr_apply split) boundExprRaw
           ole =
               OpenLet $
               SL.singleton $
               OpenLetEntry
               { ol_close = \inE -> ELet $ Annotated a $ Let boundVar boundExpr' inE
               , ol_bind = S.singleton v
               , ol_free = getFreeVars (S.singleton v) boundExpr'
               }
       pure
           ( ole <> sr_pass split
           , inVal
           )

applyOpenLet :: OpenLet a -> Expr a -> Expr a
applyOpenLet ol expr =
    trace ("Apply: " <> show (F.toList (ol_stack ol))) $
    foldl' apply expr (reverse $ fmap ol_close $ F.toList $ ol_stack ol)
    where
      apply e f = f e

freeList :: Monad m => a -> [Expr a] -> m (OpenLet a, Expr a)
freeList ann vals =
    do fillVals <-
           fmap unzip $
           forM vals $ \val -> floatLet val
       pure (mconcat (fst fillVals), EList $ Annotated ann (snd fillVals))

freeRecord :: Monad m => a -> Record (Expr a) -> m (OpenLet a, Expr a)
freeRecord ann (Record hm) =
    do fillVals <-
           fmap unzip $
           forM (HM.toList hm) $ \(key, val) ->
           do (ol, val') <- floatLet val
              pure (ol, (key, val'))
       pure (mconcat (fst fillVals),
           ERecord $ Annotated ann $ Record $ HM.fromList (snd fillVals))

freeRecordMerge :: Monad m => a -> RecordMerge a -> m (OpenLet a, Expr a)
freeRecordMerge a rm =
    do (ol, tgt') <- floatLet (rm_target rm)
       (ols, mergeIns) <- unzip <$> mapM floatLet (rm_mergeIn rm)
       pure
           ( mconcat (ol : ols)
           , ERecordMerge $ Annotated a $ rm { rm_target = tgt', rm_mergeIn = mergeIns}
           )

freeLambda :: Monad m => a -> Lambda a -> m (OpenLet a, Expr a)
freeLambda a lambda =
    do let boundHere = S.fromList $ map a_value (l_args lambda)
       (ol, body') <- floatLet (l_body lambda)
       let split = splitOpenLet boundHere ol
       pure
           ( sr_pass split
           , ELambda $ Annotated a $
             lambda { l_body = applyOpenLet (sr_apply split) body'}
           )

freeBinOp :: Monad m => a -> BinOp a -> m (OpenLet a, Expr a)
freeBinOp ann bo =
    case bo of
      BoAdd a b -> go BoAdd a b
      BoSub a b -> go BoSub a b
      BoMul a b -> go BoMul a b
      BoDiv a b -> go BoDiv a b
      BoEq a b -> go BoEq a b
      BoOr a b -> go BoOr a b
      BoGt a b -> go BoGt a b
      BoLt a b -> go BoLt a b
      BoNeq a b -> go BoNeq a b
      BoAnd a b -> go BoAnd a b
      BoGtEq a b -> go BoGtEq a b
      BoLtEq a b -> go BoLtEq a b
      BoNot x ->
          do (ol, x') <- floatLet x
             pure (ol, EBinOp $ Annotated ann $ BoNot x')
    where
      go pack l r =
          do (ol1, l') <- floatLet l
             (ol2, r') <- floatLet r
             pure (ol1 <> ol2, EBinOp $ Annotated ann $ pack l' r')

freeFunApp :: Monad m => a -> FunApp a -> m (OpenLet a, Expr a)
freeFunApp ann fa =
    do (ol1, recv) <- floatLet (fa_receiver fa)
       (ols, args) <- unzip <$> mapM floatLet (fa_args fa)
       pure
           ( mconcat (ol1 : ols)
           , EFunApp $ Annotated ann $ fa { fa_receiver = recv, fa_args = args}
           )

freeIf :: Monad m => a -> If a -> m (OpenLet a, Expr a)
freeIf ann ifE =
    do (ols, bodies) <-
           fmap unzip $
           forM (if_bodies ifE) $ \(cond, val) ->
           do (o1, cond') <- floatLet cond
              (o2, val') <- floatLet val
              pure (o1 <> o2, (cond', val'))
       (ol1, else') <- floatLet (if_else ifE)
       pure
           ( mconcat (ol1 : ols)
           , EIf $ Annotated ann $ ifE { if_bodies = bodies, if_else = else'}
           )

freeCase :: Monad m => a -> Case a -> m (OpenLet a, Expr a)
freeCase ann caseE =
    do (ol1, matchOn) <- floatLet (c_matchOn caseE)
       (ols, cases) <-
           fmap unzip $
           forM (c_cases caseE) $ \(pat, expr) ->
           do let patVars = S.fromList $ patternVars pat
              (olE, expr') <- floatLet expr
              let split = splitOpenLet patVars olE
              pure (sr_pass split, (pat, applyOpenLet (sr_apply split) expr'))
       pure
           ( mconcat (ol1 : ols)
           , ECase $ Annotated ann $ caseE { c_matchOn = matchOn, c_cases = cases }
           )

floater :: Expr a -> Expr a
floater expr =
    runIdentity $
    do (openLet, e) <- floatLet expr
       pure $ applyOpenLet openLet e

floatLet :: Monad m => Expr a -> m (OpenLet a, Expr a)
floatLet expr =
    case expr of
      ELit _ -> pure (emptyOpenLet, expr)
      EVar _ -> pure (emptyOpenLet, expr)
      EList (Annotated x listVals) -> freeList x listVals
      ERecord (Annotated x r) -> freeRecord x r
      ERecordAccess (Annotated x (RecordAccess recE field)) ->
          do (floated, e') <- floatLet recE
             pure (floated, ERecordAccess $ Annotated x $ RecordAccess e' field)
      ERecordMerge (Annotated x recMergeE) -> freeRecordMerge x recMergeE
      ELambda (Annotated x lambdaE) -> freeLambda x lambdaE
      EBinOp (Annotated x binopE) -> freeBinOp x binopE
      EFunApp (Annotated x funAppE) -> freeFunApp x funAppE
      EIf (Annotated x ifE) -> freeIf x ifE
      ECase (Annotated x caseE) -> freeCase x caseE
      ELet (Annotated x l) ->
          do (ol, e) <- toOpenLet x l
             (ol2, e') <- floatLet e
             pure (combineOpenLet ol ol2, e')
      ECopy e ->
          do (floated, e') <- floatLet e
             pure (emptyOpenLet, ECopy $ applyOpenLet floated e')

getFreeVars :: Set Var -> Expr a -> Set Var
getFreeVars seen e =
    vs_free $ snd $ runIdentity $
    runStateT (collectFreeVariables e) (VarSet seen mempty)

data VarSet
    = VarSet
    { vs_seen :: Set Var
    , vs_free :: Set Var
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
    modify $ \vs -> vs { vs_free = S.insert v (vs_free vs) }

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
