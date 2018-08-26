module Test.CopyAnalysisSpec where

import Flow.CopyAnalysis
import Test.Helpers

import Parser.Expr
import Parser.Shared
import TypeCheck.InferExpr
import Types.Ast
import Types.Common

import Control.Monad
import Data.Bifunctor
import Data.Functor.Identity
import Data.Monoid
import Test.Hspec
import Text.Megaparsec (eof)
import Text.Megaparsec.Error
import qualified Data.Text as T
import qualified Data.Text.IO as T

prettyWriteTarget :: WriteTarget -> T.Text
prettyWriteTarget wt =
    case wt of
      WtVar (Var x) -> x
      WtRecordKey (Var x) path -> x <> "." <> T.intercalate "." (fmap unRecordKey path)
      WtMany many -> "(" <> T.intercalate "|" (fmap prettyWriteTarget many) <> ")"
      WtNone -> "~"

makeWriteTargetTests :: SpecWith ()
makeWriteTargetTests =
    do testCandidates <-
           runIO $ getDirectoryFilePairs "testcode/write-target/expr" ".rcs" ".txt"
       forM_ testCandidates $ \(inFile, outFile) ->
           it ("Correctly finds write target for " ++ inFile) $
           do content <- T.readFile inFile
              expectedWriteTarget <-
                  case outFile of
                    Nothing -> fail ("Missing out file for " <> show inFile)
                    Just ok -> T.strip <$> T.readFile ok
              let parseResult =
                      first parseErrorPretty $
                      executeParser inFile (exprP <* eof) content
                  typeCheckResult = first show . runIdentity . runInferM . inferExpr
              case parseResult >>= typeCheckResult of
                Right (typedExpr, _) ->
                    (prettyWriteTarget $ findWriteTarget typedExpr []) `shouldBe`
                    expectedWriteTarget
                Left errMsg ->
                    expectationFailure $
                    "Failed to typecheck. Error: " <> errMsg
