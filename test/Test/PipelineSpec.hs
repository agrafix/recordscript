module Test.PipelineSpec
    ( runPipelineSpec )
where

import Pipeline

import Control.Monad
import Data.Monoid
import Data.Yaml
import System.Directory
import System.Exit
import System.FilePath
import System.IO.Temp
import System.Process.Typed
import Test.Hspec
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.IO as T

data TestCase
    = TestCase
    { tc_code :: T.Text
    , tc_jsCode :: Maybe T.Text
    , tc_output :: Maybe T.Text
    , tc_error :: Maybe T.Text
    } deriving (Show, Eq)

instance FromJSON TestCase where
    parseJSON =
        withObject "TestCase" $ \v ->
        TestCase
        <$> v .: "code"
        <*> v .:? "javascript"
        <*> v .:? "output"
        <*> v .:? "error"

showError :: Error -> T.Text
showError e =
    case e of
      EParseError eMsg -> "Parse Error:\n" <> eMsg
      ETypeError eMsg -> "Type Error:\n" <> eMsg
      EFlowError eMsg -> "Flow Error:\n" <> eMsg

runPipelineSpec :: SpecWith ()
runPipelineSpec =
    do allFiles <- runIO $ listDirectory ("testcode" </> "pipeline")
       let getFilesWithExt ext = filter (\fp -> takeExtension fp == ext)
           tests = getFilesWithExt ".yaml" allFiles
           runNodeExpr expr =
               withSystemTempDirectory "test" $ \dir ->
               do T.writeFile (dir </> "expr.js") $ "console.log(" <> expr <> ")"
                  readProcess $ setWorkingDir dir (shell "node expr.js")
       forM_ tests $ \testFile ->
           do testCase <-
                  runIO $ decodeFileEither ("testcode" </> "pipeline" </> testFile) >>= \parsed ->
                  case parsed of
                    Left err -> fail (show err)
                    Right ok -> pure ok
              it ("passes " <> testFile) $
                  do case compileCode (tc_code testCase) of
                       Left errMsg ->
                           case tc_error testCase of
                             Just errMsg2 ->
                                 showError errMsg `shouldBe` errMsg2
                             Nothing ->
                                 fail (T.unpack $ "Did not expect error: " <> showError errMsg)
                       Right compiledCode ->
                           do case tc_jsCode testCase of
                                Just expectedOutput ->
                                    T.strip compiledCode `shouldBe` T.strip expectedOutput
                                Nothing -> pure ()
                              case tc_output testCase of
                                 Just expectedOut ->
                                     do (exit, stdOut, _) <- runNodeExpr compiledCode
                                        exit `shouldBe` ExitSuccess
                                        T.strip (T.decodeUtf8 (BSL.toStrict stdOut)) `shouldBe`
                                            T.strip expectedOut
                                 Nothing -> pure ()
