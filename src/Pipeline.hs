module Pipeline
    ( compileCode
    , Error(..)
    )
where

import CodeGen.Js (genExpr, forceExpr, runCodeGenM, renderToText)
import Desugar.UniqueVars
import Flow.CopyAnalysis (runAnalysisM, writePathAnalysis, prettyCopyError, emptyEnv)
import Parser.Expr
import Parser.Shared
import TypeCheck.InferExpr (runInferM, inferExpr, prettyInferError)

import Data.Bifunctor
import Data.Functor.Identity
import Language.JavaScript.Parser.AST
import Text.Megaparsec (eof)
import Text.Megaparsec.Error
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL

data Error
   = EParseError T.Text
   | ETypeError T.Text
   | EFlowError T.Text
   deriving (Show, Eq)

compileCode :: T.Text -> Either Error T.Text
compileCode inputCode =
    do parseResult <-
           first (EParseError . T.pack . parseErrorPretty) $
           executeParser "<test>" (exprP <* eof) inputCode
       let uniqueResult = runUniqueM $ runUniquify parseResult
       typeCheckResult <-
           first (ETypeError . prettyInferError) $
           second fst $
           runIdentity $ runInferM (inferExpr uniqueResult)
       flowResult <-
           first (EFlowError . prettyCopyError) $
           second snd $
           runAnalysisM (writePathAnalysis typeCheckResult emptyEnv)
       pure $ TL.toStrict $ renderToText $
           JSAstExpression (runCodeGenM (genExpr flowResult >>= forceExpr)) JSNoAnnot
