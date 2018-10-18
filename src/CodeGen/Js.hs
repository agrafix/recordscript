module CodeGen.Js
    ( genExpr
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
           do v' <- genExpr v
              pure (k, v')
       let packKv (RecordKey k, v) =
               JSPropertyNameandValue (JSPropertyIdent JSNoAnnot (T.unpack k)) JSNoAnnot [v]
           contents =
               JSCTLNone $
               case transformed of
                 [] -> JSLNil
                 [x] -> JSLOne (packKv x)
                 (x:xs) ->
                     foldl' (\prev y -> JSLCons prev JSNoAnnot (packKv y)) (JSLOne (packKv x)) xs
       pure $ JSObjectLiteral JSNoAnnot contents JSNoAnnot

genIf :: CodeGenM m => If a -> m JSExpression
genIf (If bodies elseE) =
    loop bodies
    where
      loop xs =
          case xs of
            [] -> genExpr elseE
            (y:ys) ->
                do rest <- loop ys
                   packPair y rest
      packPair (condE, bodyE) elseVal =
          do cond <- genExpr condE
             body <- genExpr bodyE
             pure $
                 flip (JSExpressionParen JSNoAnnot) JSNoAnnot $
                 JSExpressionTernary cond JSNoAnnot body JSNoAnnot elseVal

genExpr :: CodeGenM m => Expr a -> m JSExpression
genExpr expr =
    case expr of
      ELit (Annotated _ lit) -> pure (genLiteral lit)
      EVar (Annotated _ (Var v)) -> pure (JSLiteral JSNoAnnot (T.unpack v))
      EList (Annotated _ exprs) ->
          do exprs' <- mapM genExpr exprs
             let contents =
                     intersperse (JSArrayComma JSNoAnnot) $
                     map JSArrayElement exprs'
             pure $ JSArrayLiteral JSNoAnnot contents JSNoAnnot
      ERecord (Annotated _ recE) -> genRecord recE
      EIf (Annotated _ ifE) -> genIf ifE
      _ -> error "undefined"
