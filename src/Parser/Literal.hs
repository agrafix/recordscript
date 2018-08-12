module Parser.Literal
    ( literal )
where

import Parser.Shared
import Types.Ast

import Data.Char (isDigit, digitToInt)
import Data.List (foldl')
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Data.Text as T
import qualified Text.Megaparsec.Char.Lexer as L

bool :: Parser Bool
bool =
    True <$ symbol "true" <|>
    False <$ symbol "false"

charP :: Parser Char
charP = between (char '\'') (char '\'') letterChar

stringP :: Parser T.Text
stringP = T.pack <$> (char '"' >> manyTill L.charLiteral (char '"'))

numberWithLength :: Parser (Int, Int)
numberWithLength =
    do number <- takeWhile1P (Just "digit") isDigit
       pure (mkNum number, T.length number)
    where
        mkNum = foldl' step 0 . T.unpack
        step a c = a * 10 + fromIntegral (digitToInt c)

numberP :: Parser Literal
numberP =
    do sign <- optional $ lexeme (char '-')
       let wrap :: Num a => a -> a
           wrap x =
               case sign of
                 Nothing -> x
                 Just _ -> negate x
       number <- L.decimal
       orFloat <-
           optional $
           do _ <- char '.'
              (parsedNumber, numberLength) <- numberWithLength
              pure $ LFloat $ wrap $
                  fromIntegral number + (fromIntegral parsedNumber * 10 ^^ negate numberLength)
       case orFloat of
         Nothing -> pure (LInt $ wrap number)
         Just f -> pure f

literal :: Parser Literal
literal =
    (numberP <?> "number") <|>
    LChar <$> charP <|>
    LString <$> stringP <|>
    LBool <$> bool
