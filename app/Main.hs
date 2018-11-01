module Main where

import Pipeline

import Data.Monoid
import System.Environment
import qualified Data.Text as T
import qualified Data.Text.IO as T

main :: IO ()
main =
    do args <- getArgs
       case args of
         ["-f", fileName] ->
             T.readFile fileName >>= \expr ->
             case compileCode expr of
               Left (EParseError msg) -> T.putStrLn ("Parse error: \n" <> msg)
               Left (ETypeError msg) -> T.putStrLn ("Type error: \n" <> msg)
               Left (EFlowError msg) -> T.putStrLn ("Flow error: \n" <> msg)
               Right ok -> T.putStrLn ok
         ["-e", expr] ->
             case compileCode (T.pack expr) of
               Left (EParseError msg) -> T.putStrLn ("Parse error: \n" <> msg)
               Left (ETypeError msg) -> T.putStrLn ("Type error: \n" <> msg)
               Left (EFlowError msg) -> T.putStrLn ("Flow error: \n" <> msg)
               Right ok -> T.putStrLn ok
         _ -> putStrLn "Usage: -e 'expression' OR -f 'filename'"
