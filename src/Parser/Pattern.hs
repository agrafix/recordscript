module Parser.Pattern
    ( patternP )
where

import Parser.Literal
import Parser.Shared
import Types.Ast
import Types.Common

import Text.Megaparsec hiding (Pos)
import Text.Megaparsec.Char

patternP :: Parser (Pattern Pos)
patternP =
    do pos <- myPos
       body pos
    where
        body pos =
            PAny pos <$ char '_' <|>
            PLit <$> posAnnotated literal <|>
            PVar <$> posAnnotated var <|>
            PRecord <$> posAnnotated (record RpmNormal patternP)
