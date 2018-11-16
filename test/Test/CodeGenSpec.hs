module Test.CodeGenSpec where

import CodeGen.Js
import Flow.CopyAnalysis
import Test.Helpers

import Parser.Expr
import Parser.Shared
import TypeCheck.InferExpr
import Types.Annotation
import Types.Ast (mapAnn, Expr)

import Control.Monad
import Data.Bifunctor
import Data.Functor.Identity
import Data.Monoid
import Language.JavaScript.Parser.AST
import Test.Hspec
import Text.Megaparsec (eof)
import Text.Megaparsec.Error
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as TL


doTc :: Monad f => Expr Pos -> f (Expr TypedPos)
doTc expr =
    case runIdentity $ runInferM (inferExpr expr) of
       Right (typedExpr, inferState) ->
           pure $ resolvePass typedExpr inferState
       Left typeError -> fail (show typeError)

makeCodeGenTests :: FilePath -> SpecWith ()
makeCodeGenTests dir =
    do testCandidates <-
           runIO $ getDirectoryFilePairs dir ".rcs" ".js"
       forM_ testCandidates $ \(inFile, outFile) ->
           it ("Correctly compiles " ++ inFile) $
           do content <- T.readFile inFile
              expected <-
                  case outFile of
                    Nothing -> pure ""
                    Just ok -> T.strip <$> T.readFile ok
              let parseResult =
                      first parseErrorPretty $
                      executeParser inFile (exprP <* eof) content
              case parseResult of
                Right parsedOk ->
                    do checked <- doTc parsedOk
                       let result = runAnalysisM $ writePathAnalysis checked emptyEnv
                       case result of
                         Left errMsg ->
                             expectationFailure $
                             "Failed to do copy analysis: " <> show errMsg
                         Right (_, finalE) ->
                             do finalTc <- doTc (mapAnn tp_pos finalE)
                                let generated =
                                        TL.toStrict $
                                        renderToText $
                                        JSAstExpression (runCodeGenM (genExpr finalTc >>= forceExpr))
                                        JSNoAnnot
                                generated `shouldBe` expected
                Left errMsg ->
                    expectationFailure $
                    "Failed to parse. Error: " <> errMsg
