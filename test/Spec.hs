import Test.ParserPrettySpec

import Parser.Expr
import Parser.Shared
import Pretty.Types
import TypeCheck.InferExpr
import Types.Ast
import Types.Types

import Control.Monad
import Data.Bifunctor
import Data.Functor.Identity
import Data.List (find)
import Data.Monoid
import System.Directory
import System.FilePath
import Test.Hspec
import Text.Megaparsec (eof)
import Text.Megaparsec.Error
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T
import qualified Data.Text.IO as T

getDirectoryFilePairs :: FilePath -> String -> String -> IO [(FilePath, Maybe FilePath)]
getDirectoryFilePairs dir ext1 ext2 =
    do allFiles <- listDirectory dir
       let getFilesWithExt ext = filter (\fp -> takeExtension fp == ext)
           ext1Candidates = getFilesWithExt ext1 allFiles
           ext2Candidates = getFilesWithExt ext2 allFiles
       pure $ flip map ext1Candidates $ \candidate ->
           let noExt = dropExtension candidate
               ext2Candidate = find (\c -> dropExtension c == noExt) ext2Candidates
           in (dir </> candidate, fmap (\x -> dir </> x) ext2Candidate)

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

formatInferState :: InferState -> T.Text
formatInferState is =
    "Var types: \n"
    <> (T.intercalate "\n" $ map mkEntry $ HM.toList $ ctx_varTypes $ is_context is)
    <> "\n Equiv map: \n"
    <> (T.intercalate "\n" $ map mkEquivEntry $ HM.toList $ ctx_equivMap $ is_context is)
    where
      mkEquivEntry (TypeVar x, ty) =
          x <> " --> " <> prettyType ty
      mkEntry (Var x, ty) =
          x <> " --> " <> prettyType ty

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
                  typeCheckResult = first show . runIdentity . runInferM . inferExpr
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
