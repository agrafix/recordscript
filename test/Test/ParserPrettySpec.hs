module Test.ParserPrettySpec where

import Parser.Literal
import Parser.Shared
import Pretty.Literal
import Types.Ast

import Data.Bifunctor
import Test.Hspec
import Text.Megaparsec (eof)
import Text.Megaparsec.Error
import qualified Data.Text as T

roundTrip :: (Eq x, Show x) => x -> (x -> T.Text) -> Parser p -> (p -> x) -> Expectation
roundTrip value pretty parse unwrap =
    do let pv = pretty value
           parseResult =
               first parseErrorPretty $
               executeParser "<test>" (parse <* eof) pv
       second unwrap parseResult `shouldBe` Right value

literalSpec :: Spec
literalSpec =
    do it "works for ints" $ roundTrip (LInt 3) prettyLiteral literal id
       it "works for negative ints" $ roundTrip (LInt (-3)) prettyLiteral literal id
       it "works for floats" $ roundTrip (LFloat 3) prettyLiteral literal id
       it "works for negative floats" $ roundTrip (LFloat (-3)) prettyLiteral literal id
       it "works for chars" $ roundTrip (LChar 'x') prettyLiteral literal id
       it "works for strings" $ roundTrip (LString "Hello from the air") prettyLiteral literal id
       it "works for bools" $
           do roundTrip (LBool False) prettyLiteral literal id
              roundTrip (LBool True) prettyLiteral literal id

parserPrettySpec :: Spec
parserPrettySpec =
    do describe "literals" literalSpec
