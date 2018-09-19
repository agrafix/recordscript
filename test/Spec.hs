import Test.CopyAnalysisSpec
import Test.Helpers
import Test.ParserPrettySpec

import Parser.Expr
import Parser.Shared
import Pretty.Types
import TypeCheck.InferExpr
import Types.Ast

import Control.Monad
import Data.Bifunctor
import Data.Functor.Identity
import Data.Monoid
import Test.Hspec
import Text.Megaparsec (eof)
import Text.Megaparsec.Error
import qualified Data.Text as T
import qualified Data.Text.IO as T

makeParserTests :: SpecWith ()
makeParserTests =
    do testCandidates <-
           runIO $ getDirectoryFilePairs "testcode/parser/expr" ".rcs" ".txt"
       forM_ testCandidates $ \(inFile, _) ->
           it ("Parses " ++ inFile) $
           do content <- T.readFile inFile
              let parseResult =
                      first parseErrorPretty $ executeParser inFile (exprP <* eof) content
              parseResult `shouldSatisfy` \x ->
                  case x of
                    Left _ -> False
                    Right _ -> True

makeTypeCheckerTests :: SpecWith ()
makeTypeCheckerTests =
    do testCandidates <-
           runIO $ getDirectoryFilePairs "testcode/type-checker/expr" ".rcs" ".txt"
       forM_ testCandidates $ \(inFile, outFile) ->
           it ("Correctly type checks " ++ inFile) $
           do content <- T.readFile inFile
              expectedTypeString <-
                  case outFile of
                    Nothing -> fail ("Missing out file for " <> show inFile)
                    Just ok -> T.strip <$> T.readFile ok
              let parseResult =
                      first parseErrorPretty $
                      executeParser inFile (exprP <* eof) content
                  typeCheckResult =
                      first (T.unpack . prettyInferError) . runIdentity . runInferM . inferExpr
                  formatType (expr, inferState) =
                      prettyType $ getExprType $ resolvePass expr inferState
              case parseResult >>= typeCheckResult of
                Right v | formatType v == expectedTypeString -> pure ()
                Right otherType@(_, inferState) ->
                    expectationFailure $ T.unpack $
                    "Expression returned wrong type. \n Expected: \n"
                    <> expectedTypeString <> "\n Got: \n"
                    <> formatType otherType <> "\n Internal state: \n"
                    <> formatInferState inferState
                Left errMsg ->
                    expectationFailure $
                    "Failed to typecheck. Error: " <> errMsg

main :: IO ()
main =
    hspec $
    do describe "Parser" makeParserTests
       describe "Parser <-> Pretty roundTrip" parserPrettySpec
       describe "Type checker" makeTypeCheckerTests
       describe "Write target" makeWriteTargetTests
       describe "Arg dependency" makeArgDepTests
