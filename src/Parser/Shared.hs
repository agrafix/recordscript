module Parser.Shared where

import Types.Ast
import qualified Types.Common as TC

import Control.Applicative (empty)
import Control.Monad (void)
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void T.Text

executeParser ::
    String -> Parser a -> T.Text -> Either (ParseError (Token T.Text) Void) a
executeParser fp p inp = runParser p fp inp

lineComment :: Parser ()
lineComment = L.skipLineComment "//"

scn :: Parser ()
scn = L.space space1 lineComment empty

sc :: Parser ()
sc = L.space (void $ takeWhile1P Nothing f) lineComment empty
  where
    f x = x == ' ' || x == '\t'

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: T.Text -> Parser T.Text
symbol = L.symbol sc

name :: Parser T.Text
name =
    T.pack <$>
    lexeme ((:) <$> letterChar <*> many alphaNumChar) <?> "name"

var :: Parser Var
var = Var <$> name

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = between (symbol "{") (symbol "}")

angles :: Parser a -> Parser a
angles = between (symbol "<") (symbol ">")

brackets :: Parser a -> Parser a
brackets = between (symbol "[") (symbol "]")

record :: Parser v -> Parser (TC.Record v)
record valP =
    braces $
    fmap (TC.Record . HM.fromList) $
    flip sepBy (symbol ",") $
    do key <- TC.RecordKey <$> name
       _ <- symbol ":"
       val <- valP
       pure (key, val)

myPos :: Parser TC.Pos
myPos =
    do pos <- getPosition
       pure $
           TC.Pos
           { TC.p_file = T.pack $ sourceName pos
           , TC.p_line = Just (unPos $ sourceLine pos)
           , TC.p_column = Just (unPos $ sourceColumn pos)
           }

posAnnotated :: Parser a -> Parser (TC.A TC.Pos a)
posAnnotated p =
    TC.Annotated <$> myPos <*> p
