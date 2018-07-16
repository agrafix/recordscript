{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
module TypeCheck.InferExpr where

import TypeCheck.InferLiteral
import Types.Ast
import Types.Common
import Types.Types
import qualified Names.StdLib as N

import Control.Monad.Except
import Control.Monad.State
import Data.Data
import Data.Monoid
import GHC.Generics
import qualified Data.Foldable as F
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.Text as T

data TypedPos
    = TypedPos
    { tp_pos :: Pos
    , tp_type :: Type
    } deriving (Show)

data InferState
    = InferState
    { is_context :: Context
    , is_varSupply :: Int
    , is_tvarSupply :: Int
    } deriving (Show)

data Context =
    Context
    { ctx_varTypes :: HM.HashMap Var Type
    , ctx_equivMap :: HM.HashMap TypeVar Type
    } deriving (Show)

data Error
    = Error
    { e_pos :: Pos
    , e_error :: ErrorMessage
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

data ErrorMessage
    = ETypeMismatch Type Type
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

type InferM m = (MonadError Error m, MonadState InferState m)

runInferM :: StateT InferState (ExceptT Error m) a -> m (Either Error (a, InferState))
runInferM go =
    runExceptT $ runStateT go initSt
    where
      initSt =
          InferState
          { is_context = initContext
          , is_varSupply = 0
          , is_tvarSupply = 0
          }
      initContext =
          Context
          { ctx_varTypes = mempty
          , ctx_equivMap = mempty
          }

freshTypeVar :: InferM m => m TypeVar
freshTypeVar =
    do s <- get
       put $ s { is_tvarSupply = is_tvarSupply s + 1 }
       pure $ TypeVar $ T.pack $ "@internal" ++ (show $ is_tvarSupply s)

assignTVar :: InferM m => Pos -> TypeVar -> Type -> m Type
assignTVar pos var ty =
    do s <- get
       let context = is_context s
       case HM.lookup var (ctx_equivMap context) of
         Nothing ->
             do modifyMap s $ \x -> HM.insert var ty x
                pure ty
         Just currentType ->
             do finalTy <- unifyTypes pos ty currentType
                modifyMap s $ \x -> HM.insert var finalTy x
                pure finalTy
    where
        modifyMap s f =
            put $
            s
            { is_context =
                (is_context s)
                { ctx_equivMap = f (ctx_equivMap $ is_context s)
                }
            }

putVarType :: InferM m => Pos -> Var -> Type -> m Type
putVarType pos var ty =
    do s <- get
       let context = is_context s
       case HM.lookup var (ctx_varTypes context) of
         Nothing ->
             do rawPut s ty
                pure ty
         Just currentType ->
             do finalTy <- unifyTypes pos ty currentType
                rawPut s finalTy
                pure finalTy
    where
        rawPut s finalTy =
            put $
            s
            { is_context =
                (is_context s)
                { ctx_varTypes = HM.insert var finalTy (ctx_varTypes $ is_context s)
                }
            }

getVarType :: InferM m => Pos -> Var -> m Type
getVarType pos var =
    do s <- get
       let context = is_context s
       case HM.lookup var (ctx_varTypes context) of
         Nothing ->
             do freshType <- TVar <$> freshTypeVar
                _ <- putVarType pos var freshType
                pure freshType
         Just t -> pure t

unifyRecord :: forall m. InferM m => Pos -> RecordType -> RecordType -> m RecordType
unifyRecord pos r1 r2 =
    case (r1, r2) of
      (RClosed x, ROpen y) -> openCloseMerge y x
      (ROpen x, RClosed y) -> openCloseMerge x y
      (RClosed (Record x), RClosed (Record y)) ->
          do finalType <- checkSame (hmKeys x `HS.union` hmKeys y) x y
             pure $ RClosed $ Record finalType
      (ROpen (Record x), ROpen (Record y)) ->
          do let sharedKeys = hmKeys x `HS.intersection` hmKeys y
                 newKeysX = hmKeys x `HS.difference` sharedKeys
                 newKeysY = hmKeys y `HS.difference` sharedKeys
                 fromX = hmKeyRestrict newKeysX x
                 fromY = hmKeyRestrict newKeysY y
             shared <- checkSame sharedKeys x y
             pure $ ROpen $ Record $ fromX <> fromY <> shared
    where
      openCloseMerge (Record open) (Record closed) =
          do -- this is probably not correct...
             let sharedKeys = hmKeys open `HS.intersection` hmKeys closed
             if sharedKeys /= hmKeys closed
                then throwTypeError
                else do finalType <- checkSame sharedKeys open closed
                        pure $ RClosed $ Record finalType
      hmKeys =
          HS.fromList . HM.keys
      hmKeyRestrict keys =
          HM.filterWithKey (\k _ -> k `HS.member` keys)
      checkSame keys hm1 hm2 =
          fmap HM.fromList $
          forM (F.toList keys) $ \k ->
          case (HM.lookup k hm1, HM.lookup k hm2) of
            (Just t1, Just t2) ->
                do t' <- unifyTypes pos t1 t2
                   pure (k, t')
            _ -> throwTypeError
      throwTypeError :: forall a. m a
      throwTypeError =
          throwError $ Error pos (ETypeMismatch (TRec r1) (TRec r2))

unifyTypes :: InferM m => Pos -> Type -> Type -> m Type
unifyTypes pos t1 t2 =
    case (t1, t2) of
      (TCon c1, TCon c2) ->
          if c1 == c2
          then pure t1
          else throwTypeError
      (TRec r1, TRec r2) -> TRec <$> unifyRecord pos r1 r2
      (TApp a1 a2, TApp b1 b2) ->
          do lhs <- unifyTypes pos a1 b1
             rhs <- unifyTypes pos a2 b2
             pure (TApp lhs rhs)
      (TVar x, t) -> assignTVar pos x t
      (t, TVar x) -> assignTVar pos x t
      _ -> throwTypeError
    where
      throwTypeError = throwError $ Error pos (ETypeMismatch t1 t2)


inferList :: InferM m => Pos -> [Type] -> m Type
inferList pos types =
    case types of
      [] ->
          do fresh <- freshTypeVar
             pure $ N.tList (TVar fresh)
      (x:xs) ->
          do elType <-
                 foldM (\resTy localTy -> unifyTypes pos resTy localTy) x xs
             pure $ N.tList elType

getExprType :: Expr TypedPos -> Type
getExprType expr =
    case expr of
      ELit (Annotated x _) -> tp_type x
      EVar (Annotated x _) -> tp_type x
      EList (Annotated x _) -> tp_type x
      ERecord (Annotated x _) -> tp_type x
      EIf (Annotated x _) -> tp_type x
      ELet (Annotated x _) -> tp_type x
      ELambda (Annotated x _) -> tp_type x
      EFunApp (Annotated x _) -> tp_type x
      ECase (Annotated x _) -> tp_type x

getRecordType :: Record (Expr TypedPos) -> Record Type
getRecordType (Record hm) =
    Record . HM.fromList $ flip map (HM.toList hm) $ \(lbl, typedExpr) ->
    (lbl, getExprType typedExpr)

inferRecord :: InferM m => Record (Expr Pos) -> m (Record (Expr TypedPos))
inferRecord (Record hm) =
    fmap (Record . HM.fromList) $
    forM (HM.toList hm) $ \(label, val) ->
    do ty <- inferExpr val
       pure (label, ty)

inferIf :: InferM m => Pos -> If Pos -> m (If TypedPos, Type)
inferIf pos ifStmt =
    do elseTyped <- inferExpr (if_else ifStmt)
       bodiesTyped <-
           forM (if_bodies ifStmt) $ \(cond, expr) ->
           do condTyped <- inferExpr cond
              exprTyped <- inferExpr expr
              _ <- unifyTypes pos N.tBool (getExprType condTyped)
              pure (condTyped, exprTyped)
       let elseType = getExprType elseTyped
           bodyTypes = map (\(x, _) -> getExprType x) bodiesTyped
       ifType <-
           foldM (\resTy localTy -> unifyTypes pos resTy localTy) elseType bodyTypes
       let typedIf =
               If
               { if_bodies = bodiesTyped
               , if_else = elseTyped
               }
       pure (typedIf, ifType)

inferLet :: InferM m => Pos -> Let Pos -> m (Let TypedPos, Type)
inferLet pos letStmt =
    -- todo: how to handle recursion?
    -- note that we assume that all variable names are globally unique
    -- at this point
    do let (Annotated boundAnn boundVar) = l_boundVar letStmt
       boundVarType <- getVarType pos boundVar
       boundExprTyped <- inferExpr (l_boundExpr letStmt)
       let boundExprType = getExprType boundExprTyped
       _ <- unifyTypes pos boundVarType boundExprType
       inTyped <- inferExpr (l_in letStmt)
       pure
           ( Let
             { l_boundVar = Annotated (TypedPos boundAnn boundVarType) boundVar
             , l_boundExpr = boundExprTyped
             , l_in = inTyped
             }
           , getExprType inTyped
           )

inferLambda :: InferM m => Pos -> Lambda Pos -> m (Lambda TypedPos, Type)
inferLambda _ lambdaStmt =
    do args <-
           forM (l_args lambdaStmt) $ \(Annotated p var) ->
           do varType <- getVarType p var
              pure (Annotated (TypedPos p varType) var, varType)
       body <- inferExpr (l_body lambdaStmt)
       let lambdaType = TFun (map snd args) (getExprType body)
       pure (Lambda (map fst args) body, lambdaType)

inferFunApp :: InferM m => Pos -> FunApp Pos -> m (FunApp TypedPos, Type)
inferFunApp pos funApp =
    do recvExpr <- inferExpr (fa_receiver funApp)
       argExprs <- mapM inferExpr (fa_args funApp)
       returnType <- TVar <$> freshTypeVar
       let recvType = getExprType recvExpr
           argTypes = map getExprType argExprs
           actualType = TFun argTypes returnType
       _ <- unifyTypes pos recvType actualType
       pure (FunApp recvExpr argExprs, returnType)

inferRecordPat :: InferM m => Record (Pattern Pos) -> m (Record (Pattern TypedPos))
inferRecordPat (Record hm) =
    fmap (Record . HM.fromList) $
    forM (HM.toList hm) $ \(label, val) ->
    do (typed, _) <- inferPattern val
       pure (label, typed)

getPatternType :: Pattern TypedPos -> Type
getPatternType pat =
    case pat of
      PVar (Annotated ann _) -> tp_type ann
      PLit (Annotated ann _) -> tp_type ann
      PRecord (Annotated ann _) -> tp_type ann
      PAny ann -> tp_type ann

getRecordPatternType :: Record (Pattern TypedPos) -> RecordType
getRecordPatternType (Record hm) =
    ROpen $ Record $ HM.map getPatternType hm

inferPattern :: InferM m => Pattern Pos -> m (Pattern TypedPos, Type)
inferPattern patternVal =
    case patternVal of
      PAny p ->
          do expectedType <- TVar <$> freshTypeVar
             pure (PAny (TypedPos p expectedType), expectedType)
      PVar (Annotated p var) ->
          do varType <- getVarType p var
             pure (PVar (Annotated (TypedPos p varType) var), varType)
      PLit (Annotated p lit) ->
          do let litType = inferLiteral lit
             pure (PLit (Annotated (TypedPos p litType) lit), litType)
      PRecord (Annotated p recPat) ->
          do recPatTyped <- inferRecordPat recPat
             let recType = TRec $ getRecordPatternType recPatTyped
             pure (PRecord (Annotated (TypedPos p recType) recPatTyped), recType)

inferCase :: InferM m => Pos -> Case Pos -> m (Case TypedPos, Type)
inferCase pos caseStmt =
    do matchOn <- inferExpr (c_matchOn caseStmt)
       returnType <- TVar <$> freshTypeVar
       patternMatches <-
           forM (c_cases caseStmt) $ \(pat, expr) ->
           do (patInf, patTy) <- inferPattern pat
              _ <- unifyTypes pos (getExprType matchOn) patTy
              exprInf <- inferExpr expr
              let exprTy = getExprType exprInf
              _ <- unifyTypes pos returnType exprTy
              pure (patInf, exprInf)
       pure (Case matchOn patternMatches, returnType)

inferExpr :: InferM m => Expr Pos -> m (Expr TypedPos)
inferExpr expr =
    case expr of
      ELit (Annotated p lit) ->
          do let litType = inferLiteral lit
             pure $ ELit (Annotated (TypedPos p litType) lit)
      EVar (Annotated p var) ->
          do varType <- getVarType p var
             pure $ EVar (Annotated (TypedPos p varType) var)
      EList (Annotated p exprs) ->
          do exprsTyped <- mapM inferExpr exprs
             listType <- inferList p $ map getExprType exprsTyped
             pure $ EList (Annotated (TypedPos p listType) exprsTyped)
      ERecord (Annotated p record) ->
          do recordTyped <- inferRecord record
             let recordType = TRec $ RClosed $ getRecordType recordTyped
             pure $ ERecord (Annotated (TypedPos p recordType) recordTyped)
      EIf (Annotated p ifStmt) ->
          do (ifTyped, ifType) <- inferIf p ifStmt
             pure $ EIf (Annotated (TypedPos p ifType) ifTyped)
      ELet (Annotated p letStmt) ->
          do (letTyped, letType) <- inferLet p letStmt
             pure $ ELet (Annotated (TypedPos p letType) letTyped)
      ELambda (Annotated p lambdaStmt) ->
          do (lambdaTyped, lambdaType) <- inferLambda p lambdaStmt
             pure $ ELambda (Annotated (TypedPos p lambdaType) lambdaTyped)
      EFunApp (Annotated p funApp) ->
          do (funAppTyped, funAppType) <- inferFunApp p funApp
             pure $ EFunApp (Annotated (TypedPos p funAppType) funAppTyped)
      ECase (Annotated p caseStmt) ->
          do (caseTyped, caseType) <- inferCase p caseStmt
             pure $ ECase (Annotated (TypedPos p caseType) caseTyped)

-- Testing / Playground

fakePos :: Pos
fakePos = Pos "<fake>" Nothing Nothing

fakeA :: x -> Annotated Pos x
fakeA = Annotated fakePos

example1 :: IO (Either Error (Expr TypedPos, InferState))
example1 =
    runInferM $ inferExpr $
    ELit (fakeA $ LInt 32)

example2 :: IO (Either Error (Expr TypedPos, InferState))
example2 =
    runInferM $ inferExpr $
    EList (fakeA [ELit $ fakeA $ LInt 32])

example3 :: IO (Either Error (Expr TypedPos, InferState))
example3 =
    runInferM $ inferExpr $
    EList (fakeA [ELit $ fakeA $ LChar 'a', ELit $ fakeA $ LInt 32])

example4 :: IO (Either Error (Expr TypedPos, InferState))
example4 =
    runInferM $ inferExpr $
    ELet $ fakeA $
    Let
    { l_boundVar = fakeA (Var "x")
    , l_boundExpr = ELit (fakeA $ LInt 32)
    , l_in = EList (fakeA [EVar $ fakeA $ Var "x", ELit $ fakeA $ LInt 32])
    }

example5 :: IO (Either Error (Expr TypedPos, InferState))
example5 =
    runInferM $ inferExpr $
    ELet $ fakeA $
    Let
    { l_boundVar = fakeA (Var "x")
    , l_boundExpr = ELit (fakeA $ LChar 'a')
    , l_in = EList (fakeA [EVar $ fakeA $ Var "x", ELit $ fakeA $ LInt 32])
    }
