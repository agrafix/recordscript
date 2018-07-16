import Control.Monad
import Data.Bifunctor
import Data.List (find)
import System.Directory
import System.FilePath
import Test.Hspec
import Text.Megaparsec (eof)
import Text.Megaparsec.Error
import qualified Data.Text.IO as T

import Parser.Expr
import Parser.Shared

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

main :: IO ()
main =
    hspec $
    do describe "Parser" $ makeParserTests
