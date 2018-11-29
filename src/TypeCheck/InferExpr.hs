{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
module TypeCheck.InferExpr where

import Pretty.Types
import TypeCheck.InferLiteral
import Types.Annotation
import Types.Ast
import Types.Common
import Types.Types
import qualified Names.StdLib as N

import Control.Monad.Except
import Control.Monad.State
import Data.Data
import Data.Maybe
import Data.Monoid
import GHC.Generics
import qualified Data.Foldable as F
import qualified Data.Generics as G
import qualified Data.HashMap.Strict as HM
import qualified Data.HashSet as HS
import qualified Data.Text as T

import Debug.Trace

data InferState
    = InferState
    { is_context :: Context
    , is_varSupply :: Int
    , is_tvarSupply :: Int
    } deriving (Show)

data Context
    = Context
    { ctx_varTypes :: HM.HashMap Var Type
    , ctx_equivMap :: HM.HashMap TypeVar Type
    } deriving (Show)

data Error
    = Error
    { e_pos :: Pos
    , e_error :: ErrorMessage
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

prettyInferError :: Error -> T.Text
prettyInferError e =
    "Error on " <> T.pack (show $ e_pos e) <> ": \n"
    <> prettyErrorMessage (e_error e)

data ErrorMessage
    = ETypeMismatch Type Type
    | EBadRecvType Type
    | EBinOpTypeMismatch Type [Type]
    | ERecordMergeTypeMismatch Type
    | ERecordAccessTypeMismatch Type RecordKey
    | ERecordAccessUnknown (Record Type) RecordKey
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

prettyErrorMessage :: ErrorMessage -> T.Text
prettyErrorMessage em =
    case em of
      ETypeMismatch t1 t2 ->
          "Expected type: \n"
          <> prettyType t1
          <> "\nBut got: \n"
          <> prettyType t2
      EBadRecvType t1 ->
          prettyType t1 <> " is not a function type"
      EBinOpTypeMismatch t1 ts ->
          "Invalid type for binary operation: \n"
          <> prettyType t1
          <> "\n expected one of: \n"
          <> T.intercalate "\n- " (map prettyType ts)
      ERecordMergeTypeMismatch t ->
          "Invalid merge record type: \n" <> prettyType t
      ERecordAccessTypeMismatch t (RecordKey k) ->
          "Can't access key " <> k <> " in record: \n" <> prettyType t
      ERecordAccessUnknown recordType (RecordKey k) ->
          "Invalid value for record access on key " <> k <> ": \n"
          <> prettyType (TRec $ ROpen recordType)

type InferM m = (MonadError Error m, MonadState InferState m)

resolveTypeVars :: Type -> HM.HashMap TypeVar Type -> Type
resolveTypeVars t mp =
    case t of
      TApp x y -> TApp (handleContructor x) (fmap (flip resolveTypeVars mp) y)
      TVar v -> traceTypeVar v mp
      TCon x -> TCon x
      TRec rt ->
          TRec $
          case rt of
            ROpen r -> ROpen (handleRecord r)
            RClosed r -> RClosed (handleRecord r)
      TFun args result ->
          TFun (fmap (flip resolveTypeVars mp) args) (resolveTypeVars result mp)
    where
      handleContructor x =
          case x of
            TyarVar tv ->
                case typeToReceiver (traceTypeVar tv mp) of
                  Right goodRecv -> goodRecv
                  Left badType ->
                      -- TODO: nicer error handling here I assume...
                      error $
                      "Received bad value for type variable in contructor receiver position. "
                      ++ " Got: " ++ show badType
            TyarCon _ -> x
      handleRecord (Record hm) =
          Record $ HM.map (flip resolveTypeVars mp) hm

traceTypeVar :: TypeVar -> HM.HashMap TypeVar Type -> Type
traceTypeVar tv mp =
    case HM.lookup tv mp of
      Nothing ->
          -- TODO: hmm should this be an error? probably not since there
          -- are generic functions
          TVar tv
      Just typeEquivalence -> resolveTypeVars typeEquivalence mp

resolvePass :: Expr TypedPos -> InferState -> Expr TypedPos
resolvePass e infState =
    G.everywhere (G.mkT resolveType) e
    where
      mp = ctx_equivMap $ is_context infState
      resolveType (TypedPos pos ty) = TypedPos pos (resolveTypeVars ty mp)

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

resolvedType :: InferM m => Type -> m Type
resolvedType ty =
    do ctx <- gets is_context
       pure $ resolveTypeVars ty $ ctx_equivMap ctx

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
             do modifyMap s $ HM.insert var ty
                pure ty
         Just currentType ->
             do finalTy <- unifyTypes pos ty currentType
                s' <- get -- TODO: is this correct? don't we need to find a fixpoint here?
                modifyMap s' $ HM.insert var finalTy
                pure finalTy
    where
        modifyMap s f =
            put $!
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

tryUnifyTypes :: InferM m => Pos -> Type -> Type -> m (Maybe Type)
tryUnifyTypes pos t1 t2 =
    (Just <$> unifyTypes pos t1 t2) `catchError` \_ -> pure Nothing

unifyTypes :: InferM m => Pos -> Type -> Type -> m Type
unifyTypes pos t1 t2 =
    do r <- unifyTypes' pos t1 t2
       pure $ trace (T.unpack $ "Unify: " <> prettyType t1 <> " w " <> prettyType t2 <> " -> " <> prettyType r) r

unifyTypes' :: InferM m => Pos -> Type -> Type -> m Type
unifyTypes' pos t1 t2 =
    case (t1, t2) of
      (x, y) | x == y -> pure x
      (TCon c1, TCon c2) ->
          if c1 == c2
          then pure t1
          else throwTypeError
      (TRec r1, TRec r2) -> TRec <$> unifyRecord pos r1 r2
      (TApp a1 a2, TApp b1 b2) ->
          do lhs <-
                 typeToReceiver <$> unifyTypes pos (receiverToType a1) (receiverToType b1)
             rhs <-
                 mapM (uncurry (unifyTypes pos)) $ zip a2 b2
             lhsTypeRecv <-
                 case lhs of
                   Right recv -> pure recv
                   Left badType -> throwError $ Error pos (EBadRecvType badType)
             pure (TApp lhsTypeRecv rhs)
      (TVar x, t) -> assignTVar pos x t
      (t, TVar x) -> assignTVar pos x t
      (TFun a1 r1, TFun a2 r2) ->
          do argT <- mapM (\(x, y) -> unifyTypes pos x y) (zip a1 a2)
             resT <- unifyTypes pos r1 r2
             pure (TFun argT resT)
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

type MergeMapTypes = HM.HashMap RecordKey Type

inferMerge :: forall m. InferM m => Pos -> RecordMerge Pos -> m (RecordMerge TypedPos, Type)
inferMerge pos recMerge =
    do targetTyped <- inferExpr (rm_target recMerge)
       sourcesTyped <- mapM inferExpr (rm_mergeIn recMerge)
       mergedTypeMap <-
           foldM computeMap mempty (targetTyped : sourcesTyped)
       let typedMerge =
               RecordMerge
               { rm_target = targetTyped
               , rm_mergeIn = sourcesTyped
               , rm_noCopy = rm_noCopy recMerge
               }
           mergeType =
               TRec $ RClosed $ Record mergedTypeMap
       pure (typedMerge, mergeType)
    where
        computeMap :: MergeMapTypes -> Expr TypedPos -> m MergeMapTypes
        computeMap typeMap checkingExpr =
            resolvedType (getExprType checkingExpr) >>= \resTy ->
            -- TODO: open vs close merging?
            case resTy of
              TRec (ROpen r) -> handle r typeMap
              TRec (RClosed r) -> handle r typeMap
              _ ->
                  -- TODO: is this merge correct here?
                  do let targetUnify = Record mempty
                     _ <-
                         unifyTypes pos (getExprType checkingExpr) (TRec $ ROpen targetUnify)
                     handle targetUnify typeMap

        handle :: Record Type -> MergeMapTypes -> m MergeMapTypes
        handle (Record rt) mmt =
            fmap HM.unions $
            forM (HM.toList rt) $ \(k, ty) ->
            case HM.lookup k mmt of
              Nothing ->
                  do fresh <- TVar <$> freshTypeVar
                     _ <- unifyTypes pos fresh ty
                     pure $ HM.insert k fresh mmt
              Just otherTy ->
                  do _ <- unifyTypes pos otherTy ty
                     pure mmt

inferAccess :: InferM m => Pos -> RecordAccess Pos -> m (RecordAccess TypedPos, Type)
inferAccess pos recAccess =
    do recordTyped <- inferExpr (ra_record recAccess)
       let recTy = getExprType recordTyped
       newVar <- TVar <$> freshTypeVar
       let builder =
               case recTy of
                 TRec (ROpen _) -> TRec . ROpen
                 TRec (RClosed _) -> TRec . RClosed
                 _ -> TRec . ROpen
           buildMap =
               case recTy of
                 TRec (ROpen hm) -> handleHm hm newVar
                 TRec (RClosed hm) -> handleHm hm newVar
                 _ -> HM.fromList [(fld, newVar)]
           targetUnify =
               builder $ Record buildMap
       unifiedType <-
           unifyTypes pos recTy targetUnify >>= resolvedType
       exprType <-
           case unifiedType of
             TRec (ROpen r) -> handle r
             TRec (RClosed r) -> handle r
             _ -> pure newVar
       pure (RecordAccess recordTyped fld, exprType)
    where
        fld = ra_field recAccess
        handleHm (Record hm) newVar =
            case HM.lookup fld hm of
              Just _ -> hm
              Nothing -> hm <> HM.fromList [(fld, newVar)]
        handle r@(Record hm) =
            case HM.lookup fld hm of
              Just ty -> pure ty
              Nothing -> throwError $ Error pos (ERecordAccessUnknown r fld)

inferIf :: InferM m => Pos -> If Pos -> m (If TypedPos, Type)
inferIf pos ifStmt =
    do elseTyped <- inferExpr (if_else ifStmt)
       let elseType = getExprType elseTyped
       bodiesTyped <-
           forM (if_bodies ifStmt) $ \(cond, expr) ->
           do condTyped <- inferExpr cond
              exprTyped <- inferExpr expr
              _ <- unifyTypes pos N.tBool (getExprType condTyped)
              _ <- unifyTypes pos elseType (getExprType exprTyped)
              pure (condTyped, exprTyped)
       let typedIf =
               If
               { if_bodies = bodiesTyped
               , if_else = elseTyped
               }
       pure (typedIf, elseType)

inferLet :: InferM m => Pos -> Let Pos -> m (Let TypedPos, Type)
inferLet pos letStmt =
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

inferBinOp :: InferM m => Pos -> BinOp Pos -> m (BinOp TypedPos, Type)
inferBinOp pos bo =
    case bo of
      BoAdd x y -> binOp BoAdd x y numTypes Nothing
      BoSub x y -> binOp BoSub x y numTypes Nothing
      BoMul x y -> binOp BoMul x y numTypes Nothing
      BoDiv x y -> binOp BoDiv x y numTypes Nothing
      BoGt x y -> binOp BoGt x y numTypes (Just N.tBool)
      BoLt x y -> binOp BoLt x y numTypes (Just N.tBool)
      BoGtEq x y -> binOp BoGtEq x y numTypes (Just N.tBool)
      BoLtEq x y -> binOp BoLtEq x y numTypes (Just N.tBool)
      BoAnd x y -> binOp BoAnd x y boolTypes Nothing
      BoOr x y -> binOp BoOr x y boolTypes Nothing
      BoNot x ->
          do lhsE <- inferExpr x
             returnType <- unifyTypes pos (getExprType lhsE) N.tBool
             pure (BoNot lhsE, returnType)
      BoEq x y -> binOpReq BoEq x y N.tBool
      BoNeq x y -> binOpReq BoNeq x y N.tBool
    where
        numTypes = [N.tInt, N.tFloat]
        boolTypes = [N.tBool]
        binOpReq pack lhs rhs forcedType =
            do lhsE <- inferExpr lhs
               rhsE <- inferExpr rhs
               _ <-
                   unifyTypes pos (getExprType lhsE) (getExprType rhsE)
               pure (pack lhsE rhsE, forcedType)
        binOp pack lhs rhs allowedTypes forcedType =
            do lhsE <- inferExpr lhs
               rhsE <- inferExpr rhs
               returnType <-
                   unifyTypes pos (getExprType lhsE) (getExprType rhsE)
               unifyAttempts <-
                   mapM (tryUnifyTypes pos returnType) allowedTypes
               case catMaybes unifyAttempts of
                 (x:_) -> pure (pack lhsE rhsE, fromMaybe x forcedType)
                 _ -> throwError $ Error pos (EBinOpTypeMismatch returnType allowedTypes)

inferExpr :: InferM m => Expr Pos -> m (Expr TypedPos)
inferExpr expr =
    case expr of
      ENative (Annotated p n) ->
          pure $ ENative (Annotated (TypedPos p (n_type n)) n)
      ECopy e' ->
          ECopy <$> inferExpr e'
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
             let recordType = TRec $ ROpen $ getRecordType recordTyped
             pure $ ERecord (Annotated (TypedPos p recordType) recordTyped)
      ERecordMerge (Annotated p recordMerge) ->
          do (mergeTyped, mergeType) <- inferMerge p recordMerge
             pure $ ERecordMerge (Annotated (TypedPos p mergeType) mergeTyped)
      ERecordAccess (Annotated p recordAccess) ->
          do (accessTyped, accessType) <- inferAccess p recordAccess
             pure $ ERecordAccess (Annotated (TypedPos p accessType) accessTyped)
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
      EBinOp (Annotated p binOp) ->
          do (binOpTyped, binOpType) <- inferBinOp p binOp
             pure $ EBinOp (Annotated (TypedPos p binOpType) binOpTyped)
