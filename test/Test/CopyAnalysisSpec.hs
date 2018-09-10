module Test.CopyAnalysisSpec where

import Flow.CopyAnalysis
import Test.Helpers

import Parser.Expr
import Parser.Shared
import TypeCheck.InferExpr
import Types.Annotation
import Types.Ast
import Types.Common

import Control.Monad
import Data.Bifunctor
import Data.Functor.Identity
import Data.Maybe
import Data.Monoid
import Test.Hspec
import Text.Megaparsec (eof)
import Text.Megaparsec.Error
import qualified Data.Text as T
import qualified Data.Text.IO as T

prettyWriteTarget :: WriteTarget -> T.Text
prettyWriteTarget wt =
    case wt of
      WtPrim PwtNone -> "~"
      WtPrim (PwtVar (Var x) path copyAllowed)
          | null path -> prefix
          | otherwise -> prefix <> "." <> T.intercalate "." (fmap unRecordKey path)
          where
            prefix = copyPrefix <> x
            copyPrefix =
                case copyAllowed of
                  CaBanned -> "!"
                  CaAllowed -> ""
      WtMany many ->
          "(" <> T.intercalate "|" (fmap (prettyWriteTarget . WtPrim) many) <> ")"

withTcExpr :: String -> FilePath -> ((T.Text, Expr TypedPos) -> IO ()) -> SpecWith ()
withTcExpr what dir go =
    do testCandidates <-
           runIO $ getDirectoryFilePairs dir ".rcs" ".txt"
       forM_ testCandidates $ \(inFile, outFile) ->
           it ("Correctly finds " ++ what ++ " for " ++ inFile) $
           do content <- T.readFile inFile
              expected <-
                  case outFile of
                    Nothing -> fail ("Missing out file for " <> show inFile)
                    Just ok -> T.strip <$> T.readFile ok
              let parseResult =
                      first parseErrorPretty $
                      executeParser inFile (exprP <* eof) content
                  typeCheckResult = first show . runIdentity . runInferM . inferExpr
              case parseResult >>= typeCheckResult of
                Right (typedExpr, _) -> go (expected, typedExpr)
                Left errMsg ->
                    expectationFailure $
                    "Failed to typecheck. Error: " <> errMsg

makeWriteTargetTests :: SpecWith ()
makeWriteTargetTests =
    withTcExpr "write target" "testcode/write-target/expr" $ \(expectedWriteTarget, typedExpr) ->
    (prettyWriteTarget $ writePathAnalysis typedExpr emptyEnv) `shouldBe`
    expectedWriteTarget

prettyArgDep :: [(Var, [RecordKey], CopyAllowed)] -> T.Text
prettyArgDep x =
    T.intercalate "\n" $ flip fmap x $ \(Var v, path, ca) ->
    let prefix =
            case ca of
              CaAllowed -> ""
              CaBanned -> "!"
        renderedPath =
            if null path
            then ""
            else "." <> T.intercalate "." (fmap unRecordKey path)
    in "- " <> prefix <> v <> renderedPath


makeArgDepTests :: SpecWith ()
makeArgDepTests =
    withTcExpr "write target" "testcode/arg-dep/expr" $ \(expected, typedExpr) ->
    case typedExpr of
      ELambda (Annotated _ l) ->
          prettyArgDep (catMaybes $ argumentDependency emptyFunInfo l) `shouldBe` expected
      _ ->
          expectationFailure $
          "Bad expression: " <> show typedExpr
