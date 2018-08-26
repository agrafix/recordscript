module Test.Helpers where

import Pretty.Types
import TypeCheck.InferExpr
import Types.Ast
import Types.Types

import Data.List (find)
import Data.Monoid
import System.Directory
import System.FilePath
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T

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
