module CodeGen.Js
    ( genExpr, forceExpr
    , runCodeGenM
    , renderToText
    )
where

import Types.Annotation
import Types.Ast
import Types.Common

import Control.Monad.State
import Data.Functor.Identity
import Data.List
import Language.JavaScript.Parser.AST
import Language.JavaScript.Pretty.Printer
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T

data JsState
    = JsState
    { js_varSupply :: Int }
    deriving (Show, Eq, Ord)

type CodeGenM m = (MonadState JsState m)

initState :: JsState
initState = JsState 0

_freshVar :: CodeGenM m => m Var
_freshVar =
    do s <- get
       put $ s { js_varSupply = js_varSupply s + 1 }
       pure $ Var $ T.pack $ "___var" ++ show (js_varSupply s)

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

genRecord :: CodeGenM m => Record (Expr a) -> m JSExpression
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

genIf :: CodeGenM m => If a -> m JSExpression
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

emptyObj :: JSExpression
emptyObj = JSObjectLiteral JSNoAnnot (JSCTLNone $ makeCommaList []) JSNoAnnot

data LetStack a
    = LetStack
    { _ls_binds :: [(A a Var, Expr a)]
    , _ls_expr :: JSExpression
    } deriving (Show, Eq)

exprToFunBody :: CodeGenM m => Either JSExpression (LetStack a) -> m [JSStatement]
exprToFunBody output =
    case output of
      Left e -> pure [JSReturn JSNoAnnot (Just $ makeParen e) $ JSSemi JSNoAnnot]
      Right (LetStack binds bodyE) ->
          do bindVals <-
                 forM binds $ \(Annotated _ (Var varName), boundE) ->
                 do boundVal <- genExpr boundE >>= forceExpr
                    let varDecl =
                            JSVarInitExpression (JSIdentifier JSAnnotSpace (T.unpack varName)) $
                            JSVarInit JSNoAnnot boundVal
                    pure $ JSVariable JSNoAnnot (makeCommaList [varDecl]) (JSSemi JSNoAnnot)
             let stmts =
                     bindVals ++
                     [ JSReturn JSNoAnnot (Just $ makeParen bodyE) $ JSSemi JSNoAnnot
                     ]
             pure stmts

forceExpr :: CodeGenM m => Either JSExpression (LetStack a) -> m JSExpression
forceExpr output =
    case output of
      Left e -> pure e
      Right ls ->
          do funBody <- exprToFunBody (Right ls)
             let funExpr =
                     makeParen $
                     JSFunctionExpression JSNoAnnot JSIdentNone JSNoAnnot
                     (makeCommaList []) JSNoAnnot $ JSBlock JSNoAnnot funBody JSNoAnnot
             pure $ JSCallExpression funExpr JSNoAnnot (makeCommaList []) JSNoAnnot


genFunApp :: CodeGenM m => FunApp a -> m JSExpression
genFunApp (FunApp receiverE argListE) =
    do recv <- genExpr receiverE >>= forceExpr
       args <- mapM (genExpr >=> forceExpr) argListE
       pure $
           JSCallExpression recv JSNoAnnot (makeCommaList args) JSNoAnnot

genLambda :: CodeGenM m => Lambda a -> m JSExpression
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

genRecordMerge :: CodeGenM m => RecordMerge a -> m JSExpression
genRecordMerge (RecordMerge targetE mergeInEs _) =
    do target <- genExpr targetE >>= forceExpr
       mergers <- mapM (genExpr >=> forceExpr) mergeInEs
       pure $
           JSCallExpression objAssign JSNoAnnot (makeCommaList (target:mergers)) JSNoAnnot

genCopy :: CodeGenM m => Expr a -> m JSExpression
genCopy bodyE =
    do body <- genExpr bodyE >>= forceExpr
       pure $
           JSCallExpression objAssign JSNoAnnot (makeCommaList [emptyObj, body]) JSNoAnnot

genRecordAccess :: CodeGenM m => RecordAccess a -> m JSExpression
genRecordAccess (RecordAccess recordE (RecordKey field)) =
    do body <- genExpr recordE >>= forceExpr
       pure $
           JSCallExpressionDot (makeParen body) JSNoAnnot (JSIdentifier JSNoAnnot $ T.unpack field)

genLet :: CodeGenM m => Let a -> m (Either JSExpression (LetStack a))
genLet (Let boundVar boundE inE) =
    do inVal <- genExpr inE
       case inVal of
         Left expr ->
             pure $ Right $ LetStack [(boundVar, boundE)] expr
         Right (LetStack prevBinds innerExpr) ->
             pure $ Right $ LetStack ((boundVar, boundE) : prevBinds) innerExpr

genBinOp :: CodeGenM m => BinOp a -> m JSExpression
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
      BoNot aE ->
          do a <- genExpr aE >>= forceExpr
             pure $ JSUnaryExpression (JSUnaryOpNot JSNoAnnot) a
    where
      handleBo op lE rE =
          do l <- genExpr lE >>= forceExpr
             r <- genExpr rE >>= forceExpr
             pure $ makeParen $ JSExpressionBinary l (op JSNoAnnot) r

genExpr :: CodeGenM m => Expr a -> m (Either JSExpression (LetStack a))
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
      ERecordMerge (Annotated _ recordMergeE) -> Left <$> genRecordMerge recordMergeE
      ERecordAccess (Annotated _ recordAccessE) -> Left <$> genRecordAccess recordAccessE
      EIf (Annotated _ ifE) -> Left <$> genIf ifE
      EFunApp (Annotated _ funAppE) -> Left <$> genFunApp funAppE
      ELambda (Annotated _ lambdaE) -> Left <$> genLambda lambdaE
      ECopy e -> Left <$> genCopy e
      ELet (Annotated _ letE) -> genLet letE
      EBinOp (Annotated _ binOpE) -> Left <$> genBinOp binOpE
      _ -> error "undefined"
