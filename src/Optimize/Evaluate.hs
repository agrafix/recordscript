module Optimize.Evaluate
    (evaluate)
where

import Analyse.VariableScopes
import Data.Maybe
import Types.Annotation
import Types.Ast
import Types.Common
import Types.Types

import Control.Monad.State
import Data.Functor.Identity
import qualified Data.HashMap.Strict as HM
import qualified Data.Set as S

import Data.Monoid
import Debug.Trace

evaluate :: Expr TypedPos -> Expr TypedPos
evaluate e =
    fst $ runIdentity $ runStateT (runExpr e) emptyState

data EvalState
    = EvalState
    { es_scope :: HM.HashMap Var (InlineDecl, Expr TypedPos)
    } deriving (Show, Eq)

emptyState :: EvalState
emptyState = EvalState mempty

scoped :: EvalM m => StateT EvalState m b -> m b
scoped go =
    do s <- get
       (a, _) <- runStateT go s
       pure a

data InlineDecl
    = InNever
    | InAlways
    | InTrivial
    deriving (Show, Eq)

undeclare :: EvalM m => Var -> m ()
undeclare v =
    modify $ \es ->
    es
    { es_scope = HM.delete v (es_scope es)
    }

declare :: EvalM m => Var -> InlineDecl -> Expr TypedPos -> m ()
declare v idecl e =
    modify $ \es ->
    es
    { es_scope = HM.insert v (if isLambda e then InNever else idecl, e) (es_scope es)
    }

lookupVar :: EvalM m => Var -> m (Maybe (InlineDecl, Expr TypedPos))
lookupVar v =
    do s <- get
       pure $ HM.lookup v (es_scope s)

type EvalM m = MonadState EvalState m

runList :: EvalM m => TypedPos -> [Expr TypedPos] -> m (Expr TypedPos)
runList ann vals =
    EList . Annotated ann <$> mapM runExpr vals

runIf :: EvalM m => TypedPos -> If TypedPos -> m (Expr TypedPos)
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
    EvalM m => Expr TypedPos -> (Pattern TypedPos, Expr TypedPos) -> m (BranchState, Pattern TypedPos, Expr TypedPos)
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

runCase :: EvalM m => TypedPos -> Case TypedPos -> m (Expr TypedPos)
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

runLet :: EvalM m => TypedPos -> Let TypedPos -> m (Expr TypedPos)
runLet ann (Let bv@(Annotated _ boundVar) boundExpr inExpr) =
    do let varOccurs =
               fromMaybe 0 $
               HM.lookup boundVar $ getFreeVarMap mempty inExpr
       case varOccurs of
         0 -> runExpr inExpr
         occs -> go (if occs == 1 && eff /= SeIo then InAlways else InTrivial)
    where
        eff = t_eff $ getExprType boundExpr
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

runVar :: EvalM m => TypedPos -> Var -> m (Expr TypedPos)
runVar ann var =
    do res <- lookupVar var
       case res of
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

runLambda :: EvalM m => TypedPos -> Lambda TypedPos -> m (Expr TypedPos)
runLambda ann (Lambda args body) =
    ELambda . Annotated ann <$> (Lambda args <$> runExpr body)

runBinOp :: forall m. EvalM m => TypedPos -> BinOp TypedPos -> m (Expr TypedPos)
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
            BinOp TypedPos
            -> (Double -> Double -> Double) -> Expr TypedPos -> Expr TypedPos -> m (Expr TypedPos)
        mathDbl binOp f a b =
            case (,) <$> toLiteral a <*> toLiteral b of
              Just (LInt x, LInt y) ->
                  litRes $ LFloat (f (fromIntegral x) (fromIntegral y))
              Just (LFloat x, LFloat y) -> litRes $ LFloat (f x y)
              _ -> noRun binOp
        math ::
            BinOp TypedPos
            -> (forall x. Num x => x -> x -> x) -> Expr TypedPos -> Expr TypedPos -> m (Expr TypedPos)
        math binOp f a b =
            case (,) <$> toLiteral a <*> toLiteral b of
              Just (LInt x, LInt y) ->
                  litRes $ LInt (f x y)
              Just (LFloat x, LFloat y) -> litRes $ LFloat (f x y)
              _ -> noRun binOp
        cmp ::
            BinOp TypedPos
            -> (forall x. (Ord x, Eq x) => x -> x -> Bool) -> Expr TypedPos -> Expr TypedPos -> m (Expr TypedPos)
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
            BinOp TypedPos
            -> (Bool -> Bool -> Bool) -> Expr TypedPos -> Expr TypedPos -> m (Expr TypedPos)
        bool binOp f a b =
            case (,) <$> toLiteral a <*> toLiteral b of
              Just (LBool x, LBool y) -> litRes $ LBool (f x y)
              _ -> noRun binOp

runFunApp :: EvalM m => TypedPos -> FunApp TypedPos -> m (Expr TypedPos)
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
                                       || (t_eff $ getExprType boundVal) == SeIo
                                    then declare boundVar InNever boundVal
                                    else declare boundVar InAlways boundVal
                                undeclare var
                                runExpr (l_body lambdaE)
                         let free = getFreeVars mempty newBody
                         if S.null (S.fromList lambdaArgs `S.intersection` free)
                            then pure newBody
                            else -- TODO: if not everything is applied, can we still do something??
                                 noAction
         Nothing -> noAction

runRecord :: EvalM m => TypedPos -> Record (Expr TypedPos) -> m (Expr TypedPos)
runRecord ann (Record hm) =
    do res <-
           forM (HM.toList hm) $ \(k, v) ->
           (,) k <$> runExpr v
       pure $ ERecord $ Annotated ann $ Record $ HM.fromList res

preMerge :: TypedPos -> [Expr TypedPos] -> [Expr TypedPos]
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

runRecordMerge :: EvalM m => TypedPos -> RecordMerge TypedPos -> m (Expr TypedPos)
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

runRecordAccess :: EvalM m => TypedPos -> RecordAccess TypedPos -> m (Expr TypedPos)
runRecordAccess ann rawAccess =
    do recordAccess <- recordAccessTransformM runExpr rawAccess
       case toRecord (ra_record recordAccess) of
         Just (Record hm) ->
             case HM.lookup (ra_field recordAccess) hm of
               Just expr -> pure expr
               Nothing ->
                   fail ("Internal error: bad record field!" <> show (ra_field recordAccess))
         Nothing -> pure $ ERecordAccess $ Annotated ann recordAccess

runExpr :: EvalM m => Expr TypedPos -> m (Expr TypedPos)
runExpr expr =
    case expr of
      ENative _ -> pure expr -- nothing to do here
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
