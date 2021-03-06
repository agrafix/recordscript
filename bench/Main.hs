module Main where

import Pipeline

import Control.Monad
import Data.Maybe
import Data.Monoid
import Data.Yaml
import System.Directory
import System.Environment
import System.FilePath
import System.IO.Temp
import System.Process.Typed
import qualified Data.Text as T
import qualified Data.Text.IO as T

data BenchCase
    = BenchCase
    { bc_setup :: T.Text
    , bc_run :: T.Text
    , bc_expected :: Maybe T.Text
    } deriving (Show, Eq)

instance FromJSON BenchCase where
    parseJSON =
        withObject "BenchCase" $ \v ->
        BenchCase
        <$> v .: "setup"
        <*> v .: "run"
        <*> v .:? "expected"

data Benchmark
    = Benchmark
    { b_name :: T.Text
    , b_recordscript :: BenchCase
    , b_javascript :: Maybe BenchCase
    , b_purescript :: Maybe BenchCase
    , b_elm :: Maybe BenchCase
    } deriving (Show, Eq)

instance FromJSON Benchmark where
    parseJSON =
        withObject "Benchmark" $ \v ->
        Benchmark
        <$> v .: "name"
        <*> v .: "recordscript"
        <*> v .:? "javascript"
        <*> v .:? "purescript"
        <*> v .:? "elm"


data PreparedBenchmark
    = PreparedBenchmark
    { pb_name :: T.Text
    , pb_setup :: T.Text
    , pb_run :: T.Text
    , pb_expected :: Maybe T.Text
    }

makePureScriptBenchmark :: BenchCase -> PreparedBenchmark
makePureScriptBenchmark bc =
    PreparedBenchmark
    { pb_name = "purescript"
    , pb_setup = "require('./output/Main/index');"
    , pb_run = bc_run bc
    , pb_expected = bc_expected bc
    }

makeElmBenchmark :: BenchCase -> PreparedBenchmark
makeElmBenchmark bc =
    PreparedBenchmark
    { pb_name = "elm"
    , pb_setup = "require('./elm').elm;"
    , pb_run = bc_run bc
    , pb_expected = bc_expected bc
    }

makeRecordScriptBenchmark :: BenchCase -> PreparedBenchmark
makeRecordScriptBenchmark bc =
    PreparedBenchmark
    { pb_name = "recordscript"
    , pb_setup =
            case compileCode (bc_setup bc) of
              Left err -> error $ show err
              Right ok -> ok
    , pb_run = bc_run bc
    , pb_expected = bc_expected bc
    }

makeJavaScriptBenchmark :: BenchCase -> PreparedBenchmark
makeJavaScriptBenchmark bc =
    PreparedBenchmark
    { pb_name = "javascript"
    , pb_setup = bc_setup bc
    , pb_run = bc_run bc
    , pb_expected = bc_expected bc
    }

data RunType
    = Run
    | CheckOnly
    deriving (Show, Eq)

data RunConfiguration
    = RunConfiguration
    { rc_type :: RunType
    , rc_filter :: Maybe T.Text
    }
    deriving (Show, Eq)

renderBenchmark :: RunType -> T.Text -> [PreparedBenchmark] -> T.Text
renderBenchmark runType filename pbench =
    T.unlines $ header ++ setup ++ tests ++ benchCode
    where
      benchCode =
          case runType of
            Run -> prerun ++ benchs ++ end
            CheckOnly -> []
      header =
          [ "var suite = require('chuhai');"
          ]
      setup =
          flip map pbench $ \pb ->
          "var " <> pb_name pb <> " = " <> pb_setup pb <> ";"
      benchs =
          flip concatMap pbench $ \pb ->
          [ "s.bench('" <> pb_name pb <> "', function() {"
          , "  " <> pb_run pb
          , "})"
          ]
      prerun =
          [ "suite('" <> filename <> "', function (s) {"
          ]
      tests =
          flip concatMap pbench $ \pb ->
          case pb_expected pb of
            Just expected ->
                [ "if (" <> pb_run pb <> " !== " <> expected <> ") {"
                , "  console.log('✗ Test of " <> pb_name pb <> " has failed!')"
                , "  console.log('> Got:')"
                , "  console.log(" <> pb_run pb <> ");"
                , "  console.log('> Expected:')"
                , "  console.log(" <> expected <> ");"
                , "} else {"
                , "  console.log('✔︎ Test of " <> pb_name pb <> " has passed')"
                , "}"
                ]
            Nothing -> []
      end =
          [ "});"
          ]

runBenchmarks :: RunConfiguration -> IO ()
runBenchmarks runConfig =
    do allFiles <- listDirectory "benchcode"
       elmProjectFile <- T.readFile "misc/elm-project.json"
       let getFilesWithExt ext = filter (\fp -> takeExtension fp == ext)
           nameFilter =
               case rc_filter runConfig of
                 Nothing -> const True
                 Just wantedName -> T.isInfixOf wantedName . T.pack
           benchs =
               filter nameFilter $
               getFilesWithExt ".yaml" allFiles
       forM_ benchs $ \benchmarkFile ->
           do benchmark <-
                  decodeFileEither ("benchcode" </> benchmarkFile) >>= \parsed ->
                  case parsed of
                    Left err -> fail (show err)
                    Right ok -> pure ok
              let compiled =
                      catMaybes
                      [ makeJavaScriptBenchmark <$> b_javascript benchmark
                      , makePureScriptBenchmark <$> b_purescript benchmark
                      , makeElmBenchmark <$> b_elm benchmark
                      , Just . makeRecordScriptBenchmark $ b_recordscript benchmark
                      ]
                  js = renderBenchmark (rc_type runConfig) (T.pack benchmarkFile) compiled
              withSystemTempDirectory "benchmark" $ \dir ->
                  do let run cmd =
                             runProcess_ $ setWorkingDir dir $ shell cmd
                     T.putStrLn "Writing benchmark file ..."
                     T.writeFile (dir </> "bench.js") js
                     T.putStrLn "Installing dependencies ..."
                     run "npm install chuhai@1.2.0 purescript@0.12.0 bower@1.8.4 elm@0.19.0-bugfix2"
                     case b_purescript benchmark of
                       Just bench ->
                           do run "node_modules/.bin/bower --allow-root install purescript-prelude"
                              T.writeFile (dir </> "pure.purs") (bc_setup bench)
                              run "node_modules/.bin/purs compile \"bower_components/*/src/**/*.purs\" pure.purs"
                       Nothing -> pure ()
                     case b_elm benchmark of
                       Just bench ->
                           do T.writeFile (dir </> "elm.json") elmProjectFile
                              createDirectoryIfMissing True (dir </> "src")
                              T.writeFile (dir </> "src" </> "Main.elm") (bc_setup bench)
                              run "node_modules/.bin/elm make src/Main.elm --output=elm_raw.js --optimize"
                              rawContent <- T.readFile (dir </> "elm_raw.js")
                              let content =
                                      T.replace "author$project$Main$export" "scope.elm" $
                                      T.replace "var author$project$Main$export = function" "scope.elm = function" rawContent
                              T.writeFile (dir </> "elm.js") content
                       Nothing -> pure ()
                     T.putStrLn "Benchmarking ..."
                     run "node bench.js"

main :: IO ()
main =
    do args <- getArgs
       case args of
         ["--check-only"] -> runBenchmarks $ baseRc CheckOnly
         ["-m", match, "--check-only"] ->
             runBenchmarks $ (baseRc CheckOnly) {rc_filter = Just $ T.strip $ T.pack match}
         ["--check-only", "-m", match] ->
             runBenchmarks $ (baseRc CheckOnly) {rc_filter = Just $ T.strip $ T.pack match}
         ["-m", match] ->
             runBenchmarks $ (baseRc Run) {rc_filter = Just $ T.strip $ T.pack match}
         _ -> runBenchmarks (baseRc Run)
    where
        baseRc t =
            RunConfiguration {rc_filter = Nothing, rc_type = t}
