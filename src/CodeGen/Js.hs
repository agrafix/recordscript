module CodeGen.Js
    ( genExpr, forceExpr
    , runCodeGenM
    , renderToText
    )
where

import Types.Annotation
import Types.Ast
import Types.Common
import Types.Types

import Control.Monad.State
import Data.Functor.Identity
import Data.List
import Data.Maybe
import Language.JavaScript.Parser.AST
import Language.JavaScript.Pretty.Printer
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T

import Debug.Trace

data JsState
    = JsState
    { js_varSupply :: Int }
    deriving (Show, Eq, Ord)

type CodeGenM m = (MonadState JsState m)

initState :: JsState
initState = JsState 0

freshVar :: CodeGenM m => m T.Text
freshVar =
    do s <- get
       put $ s { js_varSupply = js_varSupply s + 1 }
       pure $ T.pack $ "___var" ++ show (js_varSupply s)

runCodeGenM :: StateT JsState Identity a -> a
runCodeGenM action = runIdentity $ evalStateT action initState

genLiteral :: Literal -> JSExpression
genLiteral lit =
    case lit of
      LInt i -> JSLiteral JSNoAnnot (show i)
      LFloat f -> JSLiteral JSNoAnnot (show f)
      LChar c -> JSStringLiteral JSNoAnnot (show [c])
      LString t -> JSStringLiteral JSNoAnnot (show $ T.unpack t)
      LBool b -> JSLiteral JSNoAnnot (if b then "true" else "false")

genRecord :: CodeGenM m => Record (Expr TypedPos) -> m JSExpression
genRecord (Record recHm) =
    do let kvPairs = HM.toList recHm
       transformed <-
           flip mapM kvPairs $ \(k, v) ->
           do v' <- genExpr v >>= forceExpr
              pure (k, v')
       let packKv (RecordKey k, v) =
               JSPropertyNameandValue (JSPropertyIdent JSNoAnnot (T.unpack k)) JSNoAnnot [v]
           contents =
               JSCTLNone (makeCommaList $ map packKv transformed)
       pure $ JSObjectLiteral JSNoAnnot contents JSNoAnnot

genIf :: CodeGenM m => If TypedPos -> m JSExpression
genIf (If bodies elseE) =
    loop bodies
    where
      loop xs =
          case xs of
            [] -> genExpr elseE >>= forceExpr
            (y:ys) ->
                do rest <- loop ys
                   packPair y rest
      packPair (condE, bodyE) elseVal =
          do cond <- genExpr condE >>= forceExpr
             body <- genExpr bodyE >>= forceExpr
             pure $
                 flip (JSExpressionParen JSNoAnnot) JSNoAnnot $
                 JSExpressionTernary cond JSNoAnnot body JSNoAnnot elseVal

makeCommaList :: [a] -> JSCommaList a
makeCommaList vals =
    case vals of
      [] -> JSLNil
      [x] -> JSLOne x
      (x:xs) ->
          foldl' (\prev y -> JSLCons prev JSNoAnnot y) (JSLOne x) xs

makeIdent :: T.Text -> JSIdent
makeIdent i = JSIdentName JSNoAnnot (T.unpack i)

makeParen :: JSExpression -> JSExpression
makeParen expr = JSExpressionParen JSNoAnnot expr JSNoAnnot

objAssign :: JSExpression
objAssign = JSIdentifier JSNoAnnot "Object.assign"

makeIdentE :: T.Text -> JSExpression
makeIdentE i = JSIdentifier JSNoAnnot (T.unpack i)

emptyObj :: JSExpression
emptyObj = JSObjectLiteral JSNoAnnot (JSCTLNone $ makeCommaList []) JSNoAnnot

bindVar :: T.Text -> JSExpression -> JSStatement
bindVar varName boundVal =
    let varDecl =
            JSVarInitExpression (JSIdentifier JSAnnotSpace (T.unpack varName)) $
            JSVarInit JSNoAnnot boundVal
    in JSVariable JSNoAnnot (makeCommaList [varDecl]) (JSSemi JSNoAnnot)

stmtBlock :: [JSStatement] -> JSStatement
stmtBlock innerBody = JSStatementBlock JSNoAnnot innerBody JSNoAnnot (JSSemi JSNoAnnot)

data LetStack a
    = LetStack
    { _ls_binds :: [(A a Var, Expr a)]
    , _ls_expr :: JSExpression
    } deriving (Show, Eq)

genTcoLambdaWrapper :: CodeGenM m => Lambda TypedPos -> [JSStatement] -> m JSExpression
genTcoLambdaWrapper (Lambda args _) innerLoop =
    do let params =
               makeCommaList $
               map (\(Annotated _ (Var x)) -> makeIdent x) args
           wrapper =
               [ JSDoWhile JSNoAnnot
                 (JSStatementBlock JSNoAnnot innerLoop JSNoAnnot JSSemiAuto)
                 JSNoAnnot JSNoAnnot
                 (JSLiteral JSNoAnnot "true") JSNoAnnot (JSSemi JSNoAnnot)
               ]
       let bodyBlock =
               JSBlock JSNoAnnot wrapper JSNoAnnot
       pure $
           makeParen $
           JSFunctionExpression JSNoAnnot JSIdentNone JSNoAnnot params JSNoAnnot bodyBlock

handleTailCall :: CodeGenM m => Var -> Lambda TypedPos -> Expr TypedPos -> m (Maybe [JSStatement])
handleTailCall selfName (Lambda argLabels _) body =
    case body of
      EFunApp (Annotated _ (FunApp rcv argVals)) ->
          case rcv of
            EVar (Annotated _ var) | var == selfName ->
                do assignments <-
                       forM (zip argLabels argVals) $ \((Annotated _ (Var x)), val) ->
                       do tempVar <- freshVar
                          valE <- genExpr val >>= forceExpr
                          let computeStmt =
                                  bindVar tempVar valE
                              assignStmt =
                                  JSExpressionStatement
                                  (JSAssignExpression (makeIdentE x) (JSAssign JSNoAnnot) (makeIdentE tempVar))
                                  (JSSemi JSNoAnnot)
                          pure (computeStmt, assignStmt)
                   let (computes, assigns) = unzip assignments
                   pure $ Just (computes ++ assigns)
            _ -> pure Nothing
      _ -> pure Nothing

handleIf :: CodeGenM m => Var -> Lambda TypedPos -> WithA TypedPos If -> m JSExpression
handleIf selfName lambda (Annotated a (If bodies elseE)) =
    do let allBodies = bodies ++ [(ELit (Annotated a $ LBool True), elseE)]
       withTailCalls <-
           forM allBodies $ \(checkE, bodyE) ->
           do isTailCall <- handleTailCall selfName lambda bodyE
              pure (checkE, bodyE, isTailCall)
       let hasTailCall = isJust $ find (\(_, _, x) -> isJust x) withTailCalls
       compiledIf <-
           forM withTailCalls $ \(checkE, bodyE, tailCall) ->
           do check <- genExpr checkE >>= forceExpr
              ifBody <-
                  case tailCall of
                    Nothing -> genExpr bodyE >>= exprToFunBody
                    Just x -> pure x
              pure $
                  JSIf JSNoAnnot JSNoAnnot check JSNoAnnot $ stmtBlock ifBody
       if hasTailCall
          then genTcoLambdaWrapper lambda compiledIf
          else genLambda lambda

tcoOptimize :: CodeGenM m => Var -> Lambda TypedPos -> m JSExpression
tcoOptimize selfName l@(Lambda _ body) =
    do handledCall <- handleTailCall selfName l body
       case handledCall of
         Just tc -> genTcoLambdaWrapper l tc
         Nothing ->
             case body of
               EIf ifE -> handleIf selfName l ifE
               -- TODO: handle more tail call cases
               _ -> genLambda l

compileLetBind :: CodeGenM m => A TypedPos Var -> Expr TypedPos -> m JSExpression
compileLetBind (Annotated _ var) expr =
    case expr of
      ELambda (Annotated _ lambdaE) ->
          tcoOptimize var lambdaE
      _ -> genExpr expr >>= forceExpr

exprToFunBody :: CodeGenM m => Either JSExpression (LetStack TypedPos) -> m [JSStatement]
exprToFunBody output =
    case output of
      Left e -> pure [JSReturn JSNoAnnot (Just $ makeParen e) $ JSSemi JSNoAnnot]
      Right (LetStack binds bodyE) ->
          do bindVals <-
                 forM binds $ \(v@(Annotated _ (Var varName)), boundE) ->
                 do boundVal <- compileLetBind v boundE
                    pure $ bindVar varName boundVal
             let stmts =
                     bindVals ++
                     [ JSReturn JSNoAnnot (Just $ makeParen bodyE) $ JSSemi JSNoAnnot
                     ]
             pure stmts

forceExpr :: CodeGenM m => Either JSExpression (LetStack TypedPos) -> m JSExpression
forceExpr output =
    case output of
      Left e -> pure e
      Right (LetStack [] e) -> pure e
      Right ls ->
          do funBody <- exprToFunBody (Right ls)
             let funExpr =
                     makeParen $
                     JSFunctionExpression JSNoAnnot JSIdentNone JSNoAnnot
                     (makeCommaList []) JSNoAnnot $ JSBlock JSNoAnnot funBody JSNoAnnot
             pure $ JSCallExpression funExpr JSNoAnnot (makeCommaList []) JSNoAnnot


genFunApp :: CodeGenM m => FunApp TypedPos -> m JSExpression
genFunApp (FunApp receiverE argListE) =
    do recv <- genExpr receiverE >>= forceExpr
       args <- mapM (genExpr >=> forceExpr) argListE
       pure $
           JSCallExpression recv JSNoAnnot (makeCommaList args) JSNoAnnot

genLambda :: CodeGenM m => Lambda TypedPos -> m JSExpression
genLambda (Lambda args bodyE) =
    do let params =
               makeCommaList $
               map (\(Annotated _ (Var x)) -> makeIdent x) args
       funBody <- genExpr bodyE >>= exprToFunBody
       let bodyBlock =
               JSBlock JSNoAnnot funBody JSNoAnnot
       pure $
           makeParen $
           JSFunctionExpression JSNoAnnot JSIdentNone JSNoAnnot params JSNoAnnot bodyBlock

genRecordMerge :: CodeGenM m => RecordMerge TypedPos -> m (LetStack TypedPos)
genRecordMerge (RecordMerge targetE mergeInEs _) =
    do (bind, target) <-
           case targetE of
             (EVar _) ->
                 do varExpr <- genExpr targetE >>= forceExpr
                    pure (Nothing, varExpr)
             _ ->
                 do tempVar <- freshVar
                    pure
                        ( Just (Annotated (getExprAnn targetE) $ Var tempVar, targetE)
                        , JSLiteral JSNoAnnot (T.unpack tempVar)
                        )
       case mapMaybe toRecord mergeInEs of
         mergeRecords | length mergeRecords == length mergeInEs ->
             do assignments <-
                    fmap concat $
                    forM mergeRecords $ \(Record mergeRecord) ->
                    forM (HM.toList mergeRecord) $ \(RecordKey k, v) ->
                    do let lhs =
                               JSCallExpressionDot target JSNoAnnot
                               (JSIdentifier JSNoAnnot $ T.unpack k)
                       tempVar <- freshVar
                       pure
                           ( (Annotated (getExprAnn targetE) $ Var tempVar, v)
                           , JSAssignExpression lhs (JSAssign JSNoAnnot)
                             (JSLiteral JSNoAnnot (T.unpack tempVar))
                           )
                let (bindings, assigns) = unzip assignments
                pure $ LetStack (maybeToList bind ++ bindings) $ makeParen $
                    foldr (\l r -> JSCommaExpression l JSNoAnnot r) target assigns
         _ ->
             do mergers <- mapM (genExpr >=> forceExpr) mergeInEs
                pure $
                    LetStack (maybeToList bind) $
                    JSCallExpression objAssign JSNoAnnot (makeCommaList (target:mergers)) JSNoAnnot

genCopy :: CodeGenM m => Expr TypedPos -> m JSExpression
genCopy bodyE =
    do body <- genExpr bodyE >>= forceExpr
       pure $
           JSCallExpression objAssign JSNoAnnot (makeCommaList [emptyObj, body]) JSNoAnnot

genRecordAccess :: CodeGenM m => RecordAccess TypedPos -> m JSExpression
genRecordAccess (RecordAccess recordE (RecordKey field)) =
    do body <- genExpr recordE >>= forceExpr
       pure $
           JSCallExpressionDot (makeParen body) JSNoAnnot (JSIdentifier JSNoAnnot $ T.unpack field)

genLet :: CodeGenM m => Let TypedPos -> m (Either JSExpression (LetStack TypedPos))
genLet (Let boundVar boundE inE) =
    do inVal <- genExpr inE
       case inVal of
         Left expr ->
             pure $ Right $ LetStack [(boundVar, boundE)] expr
         Right (LetStack prevBinds innerExpr) ->
             pure $ Right $ LetStack ((boundVar, boundE) : prevBinds) innerExpr

genBinOp :: CodeGenM m => BinOp TypedPos -> m JSExpression
genBinOp bo =
    case bo of
      BoAdd a b -> handleBo JSBinOpPlus a b
      BoSub a b -> handleBo JSBinOpMinus a b
      BoMul a b -> handleBo JSBinOpTimes a b
      BoDiv a b -> handleBo JSBinOpDivide a b
      BoEq a b -> handleBo JSBinOpEq a b
      BoNeq a b -> handleBo JSBinOpNeq a b
      BoAnd a b -> handleBo JSBinOpAnd a b
      BoOr a b -> handleBo JSBinOpOr a b
      BoGt a b -> handleBo JSBinOpGt a b
      BoLt a b -> handleBo JSBinOpLt a b
      BoGtEq a b -> handleBo JSBinOpGe a b
      BoLtEq a b -> handleBo JSBinOpLe a b
      BoNot aE ->
          do a <- genExpr aE >>= forceExpr
             pure $ JSUnaryExpression (JSUnaryOpNot JSNoAnnot) a
    where
      handleBo op lE rE =
          do l <- genExpr lE >>= forceExpr
             r <- genExpr rE >>= forceExpr
             pure $ makeParen $ JSExpressionBinary l (op JSNoAnnot) r

genCaseCheck :: CodeGenM m => JSExpression -> Pattern TypedPos -> m JSExpression
genCaseCheck checkAgainst pat =
    case pat of
      PVar (Annotated _ _) -> pure $ genLiteral $ LBool True
      PAny _ -> pure $ genLiteral $ LBool True
      PLit (Annotated _ litE) ->
          pure $ JSExpressionBinary checkAgainst (JSBinOpEq JSNoAnnot) (genLiteral litE)
      PRecord (Annotated _ (Record patHm)) ->
          let handleEntry st (RecordKey recordKey, innerPattern) =
                  let recAccess =
                          JSCallExpressionDot (makeParen checkAgainst) JSNoAnnot
                          (JSIdentifier JSNoAnnot $ T.unpack recordKey)
                  in case innerPattern of
                       PVar _ -> pure st
                       PAny _ -> pure st
                       PLit _ -> genCaseCheck recAccess innerPattern
                       PRecord _ -> genCaseCheck recAccess innerPattern
          in foldM handleEntry (genLiteral $ LBool True) (HM.toList patHm)

genCaseBinds :: CodeGenM m => JSExpression -> Pattern TypedPos -> m [JSStatement]
genCaseBinds checkAgainst pat =
    case pat of
      PVar (Annotated _ (Var var)) -> pure [bindVar var checkAgainst]
      PAny _ -> pure []
      PLit _ -> pure []
      PRecord (Annotated _ (Record patHm)) ->
          let handleEntry st (RecordKey recordKey, innerPattern) =
                  let recAccess =
                          JSCallExpressionDot (makeParen checkAgainst) JSNoAnnot
                          (JSIdentifier JSNoAnnot $ T.unpack recordKey)
                  in case innerPattern of
                       PVar (Annotated _ (Var v)) -> pure (st ++ [bindVar v recAccess])
                       PAny _ -> pure st
                       PLit _ -> pure st
                       PRecord _ ->
                           do moreBinds <- genCaseBinds recAccess innerPattern
                              pure (st ++ moreBinds)
          in foldM handleEntry [] (HM.toList patHm)

genCaseSwitch :: CodeGenM m => String -> (Pattern TypedPos, Expr TypedPos) -> m JSStatement
genCaseSwitch varName (pat, expr) =
    do let checkAgainst = JSIdentifier JSNoAnnot varName
       check <- genCaseCheck checkAgainst pat
       binds <- genCaseBinds checkAgainst pat
       bodyE <- genExpr expr >>= forceExpr
       let body =
               binds
               ++ [JSReturn JSNoAnnot (Just $ makeParen bodyE) $ JSSemi JSNoAnnot]
       pure $ JSIf JSNoAnnot JSNoAnnot check JSNoAnnot
           (JSStatementBlock JSNoAnnot body JSNoAnnot $ JSSemi JSNoAnnot)

genCase :: CodeGenM m => Case TypedPos -> m JSExpression
genCase caseE =
    do fresh <- freshVar
       funBody <- mapM (genCaseSwitch (T.unpack fresh)) (c_cases caseE)
       let funExpr =
               makeParen $
               JSFunctionExpression JSNoAnnot JSIdentNone JSNoAnnot
               (makeCommaList [JSIdentName JSNoAnnot $ T.unpack fresh]) JSNoAnnot $
               JSBlock JSNoAnnot funBody JSNoAnnot
       matchOn <- genExpr (c_matchOn caseE) >>= forceExpr
       pure $
           JSCallExpression funExpr JSNoAnnot (makeCommaList [matchOn]) JSNoAnnot

genExpr :: CodeGenM m => Expr TypedPos -> m (Either JSExpression (LetStack TypedPos))
genExpr expr =
    case expr of
      ELit (Annotated _ lit) -> pure $ Left (genLiteral lit)
      EVar (Annotated _ (Var v)) -> pure $ Left (JSLiteral JSNoAnnot (T.unpack v))
      EList (Annotated _ exprs) ->
          do exprs' <- mapM (genExpr >=> forceExpr) exprs
             let contents =
                     intersperse (JSArrayComma JSNoAnnot) $
                     map JSArrayElement exprs'
             pure $ Left $ JSArrayLiteral JSNoAnnot contents JSNoAnnot
      ERecord (Annotated _ recE) -> Left <$> genRecord recE
      ERecordMerge (Annotated _ recordMergeE) -> Right <$> genRecordMerge recordMergeE
      ERecordAccess (Annotated _ recordAccessE) -> Left <$> genRecordAccess recordAccessE
      EIf (Annotated _ ifE) -> Left <$> genIf ifE
      EFunApp (Annotated _ funAppE) -> Left <$> genFunApp funAppE
      ELambda (Annotated _ lambdaE) -> Left <$> genLambda lambdaE
      ECopy e ->
          case tp_type $ getExprAnn e of
            TRec _ -> Left <$> genCopy e
            ty ->
                trace ("No copy. Type was: " ++ show ty) $
                genExpr e
      ELet (Annotated _ letE) -> genLet letE
      EBinOp (Annotated _ binOpE) -> Left <$> genBinOp binOpE
      ECase (Annotated _ caseE) -> Left <$> genCase caseE
