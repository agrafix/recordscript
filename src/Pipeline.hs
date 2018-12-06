module Pipeline
    ( compileCode
    , Error(..)
    )
where

import CodeGen.Js (genExpr, forceExpr, runCodeGenM, renderToText)
import Desugar.UniqueVars
import Flow.CopyAnalysis (runAnalysisM, writePathAnalysis, prettyCopyError, emptyEnv)
import Optimize.Evaluate
import Optimize.FloatLet
import Optimize.NamedLambda
import Parser.Expr
import Parser.Shared
import Pretty.Expr
import TypeCheck.InferExpr (runInferM, inferExpr, prettyInferError, resolvePass)
import Types.Annotation
import Types.Ast (mapAnn)

import Data.Bifunctor
import Data.Functor.Identity
import Language.JavaScript.Parser.AST
import Text.Megaparsec (eof)
import Text.Megaparsec.Error
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL

import Debug.Trace

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
       typeCheckResult <- trace "TC done" $ doTc uniqueResult
       namedLambdas <-
           trace "Naming done" $
           pure $ runNamedLambda (nameLambdas typeCheckResult)
       floated <-
           trace "Floating done" $
           pure $ floater namedLambdas
       evaled <-
           trace "Eval done" $
           pure $ evaluate floated
       let strippedTypes = mapAnn tp_pos evaled
       rechecked <- doTc strippedTypes
       flowResult <-
           trace (T.unpack $ prettyExpr rechecked) $
           first (EFlowError . prettyCopyError) $
           second snd $
           runAnalysisM (writePathAnalysis rechecked emptyEnv)
       finalChecked <- doTc (mapAnn tp_pos flowResult)
       pure $ TL.toStrict $ renderToText $
           JSAstExpression (runCodeGenM (genExpr finalChecked >>= forceExpr)) JSNoAnnot
    where
        doTc expr =
            do (typeCheckResult, inferState) <-
                   first (ETypeError . prettyInferError) $
                   runIdentity $ runInferM (inferExpr expr)
               pure $ resolvePass typeCheckResult inferState
