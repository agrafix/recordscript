module Test.CodeGenSpec where

import CodeGen.Js
import Flow.CopyAnalysis
import Test.Helpers

import Parser.Expr
import Parser.Shared
import TypeCheck.InferExpr

import Control.Monad
import Data.Bifunctor
import Data.Functor.Identity
import Data.Monoid
import Language.JavaScript.Parser.AST
import Test.Hspec
import Text.Megaparsec (eof)
import Text.Megaparsec.Error
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as TL


makeCodeGenTests :: FilePath -> SpecWith ()
makeCodeGenTests dir =
    do testCandidates <-
           runIO $ getDirectoryFilePairs dir ".rcs" ".js"
       forM_ testCandidates $ \(inFile, outFile) ->
           it ("Correctly compiles " ++ inFile) $
           do content <- T.readFile inFile
              expected <-
                  case outFile of
                    Nothing -> pure ""
                    Just ok -> T.strip <$> T.readFile ok
              let parseResult =
                      first parseErrorPretty $
                      executeParser inFile (exprP <* eof) content
                  typeCheckResult = first show . runIdentity . runInferM . inferExpr
              case parseResult >>= typeCheckResult of
                Right (typedExpr, _) ->
                    do let result = runAnalysisM $ writePathAnalysis typedExpr emptyEnv
                       case result of
                         Left errMsg ->
                             expectationFailure $
                             "Failed to do copy analysis: " <> show errMsg
                         Right (_, finalE) ->
                             do let generated =
                                        TL.toStrict $
                                        renderToText $
                                        JSAstExpression (runCodeGenM (genExpr finalE >>= forceExpr))
                                        JSNoAnnot
                                generated `shouldBe` expected
                Left errMsg ->
                    expectationFailure $
                    "Failed to typecheck. Error: " <> errMsg
