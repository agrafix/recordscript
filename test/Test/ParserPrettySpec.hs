module Test.ParserPrettySpec where

import Parser.Literal
import Parser.Shared
import Parser.Types
import Pretty.Literal
import Pretty.Types
import Types.Ast
import Types.Common
import Types.Types

import Data.Bifunctor
import Test.Hspec
import Text.Megaparsec (eof)
import Text.Megaparsec.Error
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T

roundTrip :: (Eq x, Show x) => x -> (x -> T.Text) -> Parser p -> (p -> x) -> Expectation
roundTrip value pretty parse unwrap =
    do let pv = pretty value
           parseResult =
               first parseErrorPretty $
               executeParser "<test>" (parse <* eof) pv
           errorPrefix =
               "Failed to parse: \n------\n"
               ++ T.unpack pv ++ "\n------\n"
           check res =
               case res of
                 Left errMsg ->
                     expectationFailure $
                     errorPrefix ++ errMsg
                 Right parsedVal ->
                     if parsedVal /= value
                     then expectationFailure $
                          errorPrefix
                          ++ "Parsed: " ++ show parsedVal ++ "\n"
                          ++ "Expected: " ++ show value
                     else pure ()
       check $ second unwrap parseResult

literalSpec :: Spec
literalSpec =
    do it "works for ints" $ go (LInt 3)
       it "works for negative ints" $ go (LInt (-3))
       it "works for floats" $ go (LFloat 3)
       it "works for floats 2" $ go (LFloat 3.0)
       it "works for floats 3" $ go (LFloat 3.0001)
       it "works for floats 4" $ go (LFloat 0.001)
       it "works for floats 5" $ go (LFloat 110000.0001)
       it "works for negative floats" $ go (LFloat (-3))
       it "works for chars" $ go (LChar 'x')
       it "works for strings" $ go (LString "Hello from the air")
       it "works for bools" $
           do go (LBool False)
              go (LBool True)
    where
        go e = roundTrip e prettyLiteral literal id

typeSpec :: Spec
typeSpec =
    do it "works for type variabels" $
           go (TVar (TypeVar "var"))
       it "works for type constructors" $
           go (TCon (TypeConstructor "Unit"))
       it "works for type application" $
           let arg1 = TCon (TypeConstructor "List")
               arg2 = TVar (TypeVar "a")
           in go (TApp arg1 arg2)
       it "works for open record types" $
           go $ TRec $ ROpen $ Record $
           HM.fromList [(RecordKey "foo", TVar (TypeVar "a"))]
       it "works for closed record types" $
           go $ TRec $ RClosed $ Record $
           HM.fromList [(RecordKey "foo", TVar (TypeVar "a"))]
       it "works for functions with no arguments" $
           go (TFun [] (TVar (TypeVar "a")))
       it "works for functions" $
           let arg1 = TCon (TypeConstructor "String")
               arg2 = TVar (TypeVar "a")
               res = TCon (TypeConstructor "Unit")
           in go (TFun [arg1, arg2] res)
    where
        go e =
            roundTrip e prettyType typeP id

parserPrettySpec :: Spec
parserPrettySpec =
    do describe "literals" literalSpec
       describe "types" typeSpec
