module Optimize.Evaluate
    (evaluate)
where

import Analyse.VariableScopes
import Data.Maybe
import Pretty.Expr
import Types.Annotation
import Types.Ast
import Types.Common

import Control.Monad.State
import Data.Functor.Identity
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S
import qualified Data.Text as T

import Data.Monoid
import Debug.Trace

evaluate :: Show a => Expr a -> Expr a
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

undeclare :: EvalM a m => Var -> m ()
undeclare v =
    modify $ \es ->
    es
    { es_scope = HM.delete v (es_scope es)
    }

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

type EvalM a m = (Show a, MonadState (EvalState a) m)

runList :: EvalM a m => a -> [Expr a] -> m (Expr a)
runList ann vals =
    EList . Annotated ann <$> mapM runExpr vals

runIf :: EvalM a m => a -> If a -> m (Expr a)
runIf ann rawIf =
    do evaledIf <- ifTransformM runExpr rawIf
       let ifBodies =
               filter (\(check, _) -> toLiteral check /= Just (LBool False))
               (if_bodies evaledIf)
       case trace ("If bodies:" <> show (if_bodies evaledIf)) $ ifBodies of
         ((cond, alwaysTaken):_) | isBool True cond -> pure alwaysTaken
         [] -> pure (if_else evaledIf)
         _ -> pure $ EIf $ Annotated ann $ If ifBodies (if_else evaledIf)

data BranchState
    = BsAlways
    | BsNever
    | BsMaybe
    deriving (Show, Eq)

checkCaseBranch ::
    EvalM a m => Expr a -> (Pattern a, Expr a) -> m (BranchState, Pattern a, Expr a)
checkCaseBranch matchOn (pat, branchE) =
    case pat of
      PAny _ -> pure (BsAlways, pat, branchE)
      PLit (Annotated _ lit) ->
          -- TODO: this could do better in detecting BsNever
          pure (if isLit lit matchOn then BsAlways else BsMaybe, pat, branchE)
      PVar (Annotated _ var) ->
          do branchE' <-
                 scoped $
                 do declare var InAlways matchOn
                    runExpr branchE
             pure (BsAlways, pat, branchE')
      PRecord _ -> pure (BsMaybe, pat, branchE) -- TODO: this could do better.

runCase :: EvalM a m => a -> Case a -> m (Expr a)
runCase ann rawCase =
    do evaledCase <- caseTransformM runExpr rawCase
       cases <-
           forM (c_cases evaledCase) (checkCaseBranch (c_matchOn evaledCase))
       let applicableCases =
               filter (\(check, _, _) -> check /= BsNever) cases
       case applicableCases of
         -- TODO: if there's only one case, we can remove the case statement entirely
         ((BsAlways, _, alwaysTaken):_) -> pure alwaysTaken
         [(_, _, alwaysTaken)] -> pure alwaysTaken
         _ ->
             pure $ ECase $ Annotated ann $
             Case (c_matchOn evaledCase) $ flip map applicableCases $ \(_, p, e) -> (p, e)

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
       case trace ("runVar: " <> show var <> " res:" <> show res) res of
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
         BoGt a b -> cmp binOp (>) a b
         BoGtEq a b -> cmp binOp (>=) a b
         BoLt a b -> cmp binOp (<) a b
         BoLtEq a b -> cmp binOp (<=) a b
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

runFunApp :: EvalM a m => a -> FunApp a -> m (Expr a)
runFunApp ann rawFunApp =
    do funApp <- funAppTransformM runExpr rawFunApp
       let noAction = pure $ EFunApp . Annotated ann $ funApp
       case toVar (fa_receiver funApp) of
         Just var ->
             do receiver <- lookupVar var
                case join $ fmap (toLambda . snd) receiver of
                  Nothing -> noAction
                  Just lambdaE ->
                      do let lambdaArgs = a_value <$> l_args lambdaE
                             zippedArgs =
                                 zip lambdaArgs (fa_args funApp)
                         newBody <-
                             scoped $
                             do forM_ zippedArgs $ \(boundVar, boundVal) ->
                                    if S.member boundVar (getFreeVars mempty boundVal)
                                    then declare boundVar InNever boundVal
                                    else declare boundVar InAlways boundVal
                                undeclare var
                                runExpr (l_body lambdaE)
                         let free =
                                 trace ("######## OldBody: " <> T.unpack (prettyExpr (l_body lambdaE)) <> " NewBody: " <> T.unpack (prettyExpr newBody) <> " args: " <> show (map (\(x, y) -> (x, prettyExpr y)) zippedArgs)) $
                                 getFreeVars mempty newBody
                         if S.null (S.fromList lambdaArgs `S.intersection` free)
                            then pure newBody
                            else -- TODO: if not everything is applied, can we still do something??
                                 noAction
         Nothing -> noAction

runRecord :: EvalM a m => a -> Record (Expr a) -> m (Expr a)
runRecord ann (Record hm) =
    do res <-
           forM (HM.toList hm) $ \(k, v) ->
           (,) k <$> runExpr v
       pure $ ERecord $ Annotated ann $ Record $ HM.fromList res

preMerge :: a -> [Expr a] -> [Expr a]
preMerge ann exprs =
    reverse $ looper exprs (Record mempty) []
    where
      doMerge (Record l) (Record r) = Record $ HM.union l r
      looper [] curr@(Record r) output =
          if HM.null r
          then output
          else ((ERecord $ Annotated ann curr) : output)
      looper (e:es) currentRecord@(Record r') output =
          case toRecord e of
            Just r ->
                looper es (doMerge currentRecord r) output
            Nothing ->
                let next =
                        if HM.null r'
                        then (e : output)
                        else (e : (ERecord $ Annotated ann currentRecord) : output)
                in looper es (Record mempty) next

runRecordMerge :: EvalM a m => a -> RecordMerge a -> m (Expr a)
runRecordMerge ann rawMerge =
    do (RecordMerge target mergeIn noCopy) <- recordMergeTransformM runExpr rawMerge
       let merged = preMerge ann (target : mergeIn)
       (target', mergeIn') <-
           case merged of
             [] -> fail "Internal merge error"
             (tgt:rest) -> pure (tgt, rest)
       case mergeIn' of
         [] -> pure target'
         _ -> pure $ ERecordMerge $ Annotated ann (RecordMerge target' mergeIn' noCopy)

runRecordAccess :: EvalM a m => a -> RecordAccess a -> m (Expr a)
runRecordAccess ann rawAccess =
    do recordAccess <- recordAccessTransformM runExpr rawAccess
       case toRecord (ra_record recordAccess) of
         Just (Record hm) ->
             case HM.lookup (ra_field recordAccess) hm of
               Just expr -> pure expr
               Nothing ->
                   fail ("Internal error: bad record field!" <> show (ra_field recordAccess))
         Nothing -> pure $ ERecordAccess $ Annotated ann recordAccess

runExpr :: EvalM a m => Expr a -> m (Expr a)
runExpr expr =
    case expr of
      ELit _ -> pure expr -- can't really do anything
      EVar (Annotated x varE) -> runVar x varE
      EList (Annotated x listVals) -> runList x listVals
      EIf (Annotated x ifE) -> runIf x ifE
      ELet (Annotated x letE) -> runLet x letE
      ECase (Annotated x caseE) -> runCase x caseE
      EBinOp (Annotated x binOpE) -> runBinOp x binOpE
      ELambda (Annotated x lambdaE) -> runLambda x lambdaE
      EFunApp (Annotated x funAppE) -> runFunApp x funAppE
      ERecord (Annotated x recordE) -> runRecord x recordE
      ERecordMerge (Annotated x recordMergeE) -> runRecordMerge x recordMergeE
      ERecordAccess (Annotated x recordAccessE) -> runRecordAccess x recordAccessE
      ECopy copyE ->
          -- TODO: is this safe? well, actually there should never
          -- be copies in the compiler at this stage.
          ECopy <$> runExpr copyE
