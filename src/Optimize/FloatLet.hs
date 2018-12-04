module Optimize.FloatLet
    ( floater )
where

import Analyse.VariableScopes
import Types.Annotation
import Types.Ast
import Types.Common
import Types.Types

import Control.Monad
import Data.Functor.Identity
import Data.Monoid
import Data.Set (Set)
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S
import qualified Data.SortedList as SL

import Debug.Trace

data OpenLetEntry
    = OpenLetEntry
    { ol_close :: Expr TypedPos -> Expr TypedPos
    , ol_bind :: Set Var
    , ol_free :: Set Var
    }

instance Show (OpenLetEntry) where
    show ole =
        "OpenLetEntry { ol_close = undefined, ol_bind = "
        <> show (ol_bind ole) <> ", ol_free = " <> show (ol_free ole) <> "}"

instance Eq (OpenLetEntry) where
    (/=) ol1 ol2 =
        not (S.null (ol_bind ol1 `S.intersection` ol_free ol2))

instance Ord (OpenLetEntry) where
    compare ol1 ol2 =
        if not (S.null (ol_bind ol1 `S.intersection` ol_free ol2))
        then LT
        else GT

data OpenLet
    = OpenLet
    { ol_stack :: SL.SortedList OpenLetEntry
    } deriving (Show)

emptyOpenLet :: OpenLet
emptyOpenLet = OpenLet mempty

combineOpenLet :: OpenLet -> OpenLet -> OpenLet
combineOpenLet ol1 ol2 =
    OpenLet
    { ol_stack = ol_stack ol1 <> ol_stack ol2
    }

data SplitResult
    = SplitResult
    { sr_pass :: OpenLet
      -- ^ safe to pass beyond the variable binding
    , sr_apply :: OpenLet
      -- ^ apply at current level
    }

splitOpenLet :: S.Set Var -> OpenLet -> SplitResult
splitOpenLet boundVars openLet =
    let applySpan ole =
            not (S.null (boundVars `S.intersection` ol_free ole))
        (apply, pass) =
            span applySpan $ F.toList (ol_stack openLet)
    in trace ("Split: pass=" <> show pass <> " apply=" <> show apply) $
       SplitResult
       { sr_pass = OpenLet $ SL.toSortedList pass
       , sr_apply = OpenLet $ SL.toSortedList apply
       }

instance Monoid OpenLet where
    mempty = emptyOpenLet
    mappend = combineOpenLet

toOpenLet :: Monad m => TypedPos -> Let TypedPos -> m (OpenLet, Expr TypedPos)
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

applyOpenLet :: OpenLet -> Expr TypedPos -> Expr TypedPos
applyOpenLet ol expr =
    trace ("Apply: " <> show (F.toList (ol_stack ol))) $
    foldr apply expr (fmap ol_close $ F.toList $ ol_stack ol)
    where
      apply f e = f e

freeList :: Monad m => TypedPos -> [Expr TypedPos] -> m (OpenLet, Expr TypedPos)
freeList ann vals =
    do fillVals <-
           fmap unzip $
           forM vals $ \val -> floatLet val
       pure (mconcat (fst fillVals), EList $ Annotated ann (snd fillVals))

freeRecord :: Monad m => TypedPos -> Record (Expr TypedPos) -> m (OpenLet, Expr TypedPos)
freeRecord ann (Record hm) =
    do fillVals <-
           fmap unzip $
           forM (HM.toList hm) $ \(key, val) ->
           do (ol, val') <- floatLet val
              pure (ol, (key, val'))
       pure (mconcat (fst fillVals),
           ERecord $ Annotated ann $ Record $ HM.fromList (snd fillVals))

freeRecordMerge :: Monad m => TypedPos -> RecordMerge TypedPos -> m (OpenLet, Expr TypedPos)
freeRecordMerge a rm =
    do (ol, tgt') <- floatLet (rm_target rm)
       (ols, mergeIns) <- unzip <$> mapM floatLet (rm_mergeIn rm)
       pure
           ( mconcat (ol : ols)
           , ERecordMerge $ Annotated a $ rm { rm_target = tgt', rm_mergeIn = mergeIns}
           )

freeLambda :: Monad m => TypedPos -> Lambda TypedPos -> m (OpenLet, Expr TypedPos)
freeLambda a lambda =
    do let boundHere = S.fromList $ map a_value (l_args lambda)
       (ol, body') <- floatLet (l_body lambda)
       let split = splitOpenLet boundHere ol
       pure
           ( sr_pass split
           , ELambda $ Annotated a $
             lambda { l_body = applyOpenLet (sr_apply split) body'}
           )

freeBinOp :: Monad m => TypedPos -> BinOp TypedPos -> m (OpenLet, Expr TypedPos)
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

freeFunApp :: Monad m => TypedPos -> FunApp TypedPos -> m (OpenLet, Expr TypedPos)
freeFunApp ann fa =
    do (ol1, recv) <- floatLet (fa_receiver fa)
       (ols, args) <- unzip <$> mapM floatLet (fa_args fa)
       pure
           ( mconcat (ol1 : ols)
           , EFunApp $ Annotated ann $ fa { fa_receiver = recv, fa_args = args}
           )

freeIf :: Monad m => TypedPos -> If TypedPos -> m (OpenLet, Expr TypedPos)
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

freeCase :: Monad m => TypedPos -> Case TypedPos -> m (OpenLet, Expr TypedPos)
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

freeLet :: Monad m => TypedPos -> Let TypedPos -> m (OpenLet, Expr TypedPos)
freeLet ann letE@(Let boundVar@(Annotated _ v) boundExpr inVal) =
    case t_eff (tp_type ann) of
      SeIo ->
          -- do not float side effectful things
          do (boundOlRaw, boundExprRaw) <- floatLet boundExpr
             let split = splitOpenLet (S.singleton v) boundOlRaw
                 letExprFull =
                     ELet $ Annotated ann $
                     Let boundVar boundExprRaw inVal
             pure (sr_pass split, applyOpenLet (sr_apply split) letExprFull)
      _ ->
          do (ol, e) <- toOpenLet ann letE
             (ol2, e') <- floatLet e
             pure (combineOpenLet ol ol2, e')

floater :: Expr TypedPos -> Expr TypedPos
floater expr =
    runIdentity $
    do (openLet, e) <- floatLet expr
       pure $ applyOpenLet openLet e

floatLet :: Monad m => Expr TypedPos -> m (OpenLet, Expr TypedPos)
floatLet expr =
    case expr of
      ENative _ -> pure (emptyOpenLet, expr)
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
      ELet (Annotated x l) -> freeLet x l
      ECopy e ->
          do (floated, e') <- floatLet e
             pure (emptyOpenLet, ECopy $ applyOpenLet floated e')
