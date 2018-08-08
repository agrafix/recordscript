module Parser.Types
    ( typeP )
where

import Parser.Shared
import Types.Types

import Text.Megaparsec hiding (Pos)

typeP :: Parser Type
typeP =
    try (uncurry TFun <$> funP) <|>
    try (uncurry TApp <$> tappP) <|>
    simpleTypeP

conOrVarP :: Parser Type
conOrVarP =
    TCon . TypeConstructor <$> tyConName <|>
    TVar . TypeVar <$> name

simpleTypeP :: Parser Type
simpleTypeP =
    conOrVarP <|>
    TRec <$> recP

recP :: Parser RecordType
recP =
    try (RClosed <$> record RpmStrict typeP) <|>
    ROpen <$> record RpmNormal typeP

tappP :: Parser (Type, Type)
tappP =
    (,) <$> simpleTypeP <*> angles typeP

funP :: Parser ([Type], Type)
funP =
    do args <-
           parens $ flip sepBy (symbol ",") typeP
       _ <- symbol "=>"
       bodyT <- typeP
       pure (args, bodyT)
