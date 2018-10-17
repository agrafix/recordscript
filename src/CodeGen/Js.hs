module CodeGen.Js
    ( genExpr
    , runCodeGenM
    , renderToText
    )
where

import Types.Annotation
import Types.Ast

import Control.Monad.State
import Data.Functor.Identity
import Data.List
import Language.JavaScript.Parser.AST
import Language.JavaScript.Pretty.Printer
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
      _ -> error "undefined"
