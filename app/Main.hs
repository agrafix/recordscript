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
         ["-f", fileName, "--game", gameFile] ->
             T.readFile fileName >>= \expr ->
             case compileCode expr of
               Left (EParseError msg) -> T.putStrLn ("Parse error: \n" <> msg)
               Left (ETypeError msg) -> T.putStrLn ("Type error: \n" <> msg)
               Left (EFlowError msg) -> T.putStrLn ("Flow error: \n" <> msg)
               Right ok ->
                   do let output =
                              T.concat
                              [ "<html><head><title>Game</title></head>"
                              , "<body>"
                              , "<canvas width=\"500\" height=\"500\" id=\"game\"></canvas>"
                              , "<script type=\"text/javascript\">"
                              , ok
                              , "</script></body></html>"
                              ]
                      T.writeFile gameFile output
         ["-e", expr] ->
             case compileCode (T.pack expr) of
               Left (EParseError msg) -> T.putStrLn ("Parse error: \n" <> msg)
               Left (ETypeError msg) -> T.putStrLn ("Type error: \n" <> msg)
               Left (EFlowError msg) -> T.putStrLn ("Flow error: \n" <> msg)
               Right ok -> T.putStrLn ok
         _ -> putStrLn "Usage: -e 'expression' OR -f 'filename'"
