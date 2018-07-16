module Parser.Literal
    ( literal )
where

import Parser.Shared
import Types.Ast

import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Data.Scientific as Sci
import qualified Data.Text as T
import qualified Text.Megaparsec.Char.Lexer as L

float :: Parser Double
float =  L.signed sc (lexeme (Sci.toRealFloat <$> L.scientific))

bool :: Parser Bool
bool =
    True <$ symbol "true" <|>
    False <$ symbol "false"

charP :: Parser Char
charP = between (char '\'') (char '\'') letterChar

stringP :: Parser T.Text
stringP = T.pack <$> (char '"' >> manyTill L.charLiteral (char '"'))

int :: Parser Int
int = L.signed sc (lexeme L.decimal)

literal :: Parser Literal
literal =
    LFloat <$> float <|>
    LInt <$> int <|>
    LChar <$> charP <|>
    LString <$> stringP <|>
    LBool <$> bool
