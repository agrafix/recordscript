module Test.CopyAnalysisSpec where

import Flow.CopyAnalysis
import Test.Helpers

import Parser.Expr
import Parser.Shared
import Pretty.Expr
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
      WtPrim (PwtVar (Var x) path copyAllowed writeOccured _)
          | null path -> prefix
          | otherwise -> prefix <> "." <> T.intercalate "." (fmap unRecordKey path)
          where
            prefix = writePrefix <> copyPrefix <> x
            writePrefix =
                case writeOccured of
                  WoWrite -> "#"
                  WoRead -> ""
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
                  typeCheckResult =
                      first (T.unpack . prettyInferError) . runIdentity . runInferM . inferExpr
              case parseResult >>= typeCheckResult of
                Right (typedExpr, _) -> go (expected, typedExpr)
                Left errMsg ->
                    expectationFailure $
                    "Failed to typecheck. Error: " <> errMsg

makeWriteTargetTests :: SpecWith ()
makeWriteTargetTests =
    withTcExpr "write target" "testcode/write-target/expr" $ \(expectedWriteTarget, typedExpr) ->
    do let result = runAnalysisM $ writePathAnalysis typedExpr emptyEnv
       case result of
         Left err ->
             T.replace "\n" "" (prettyCopyError err) `shouldBe` expectedWriteTarget
         Right (wt, expr) ->
             let printedExpr =
                     if expr /= typedExpr
                     then "\n=====\n" <> T.replace "\n" "" (prettyExpr expr)
                     else ""
             in (prettyWriteTarget wt <> printedExpr) `shouldBe` expectedWriteTarget

prettyArgDep :: [(Var, [RecordKey], CopyAllowed, WriteOccured, Position)] -> T.Text
prettyArgDep x =
    T.intercalate "\n" $ flip fmap x $ \(Var v, path, ca, wo, _) ->
    let prefix =
            case ca of
              CaAllowed -> ""
              CaBanned -> "!"
        prefix2 =
            case wo of
              WoRead -> ""
              WoWrite -> "#"
        renderedPath =
            if null path
            then ""
            else "." <> T.intercalate "." (fmap unRecordKey path)
    in "- " <> prefix2 <> prefix <> v <> renderedPath


makeArgDepTests :: SpecWith ()
makeArgDepTests =
    withTcExpr "write target" "testcode/arg-dep/expr" $ \(expected, typedExpr) ->
    case typedExpr of
      ELambda (Annotated _ l) ->
          do let result = runAnalysisM $ argumentDependency emptyFunInfo l
             case result of
               Left err ->
                   expectationFailure $
                   T.unpack $ prettyCopyError err
               Right ok ->
                   prettyArgDep (catMaybes ok) `shouldBe` expected
      _ ->
          expectationFailure $
          "Bad expression: " <> show typedExpr
