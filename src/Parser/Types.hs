module Parser.Types
    ( typeP )
where

import Parser.Shared
import Types.Types

import Text.Megaparsec hiding (Pos)

typeP :: Parser Type
typeP =
    Type <$> (typeValP <|> angles typeValP) <*> sideEffectP

sideEffectP :: Parser SideEffect
sideEffectP =
    do sideEffect <-
           optional $
           do _ <- symbol "::"
              _ <- symbol "io"
              pure ()
       pure $
           case sideEffect of
             Just () -> SeIo
             Nothing -> SeNone

typeValP :: Parser TypeVal
typeValP =
    try (uncurry TFun <$> funP) <|>
    try (uncurry TApp <$> tappP) <|>
    (rewrapEither TCon TVar <$> conOrVarP) <|>
    TRec <$> recP

rewrapEither :: (a -> x) -> (b -> x) -> Either a b -> x
rewrapEither l r opts =
    case opts of
      Left x -> l x
      Right y -> r y

conOrVarP :: Parser (Either TypeConstructor TypeVar)
conOrVarP =
    Left . TypeConstructor <$> tyConName <|>
    Right . TypeVar <$> name

recP :: Parser RecordType
recP =
    try (RClosed <$> record RpmStrict typeP) <|>
    ROpen <$> record RpmNormal typeP

tappP :: Parser (TypeAppReceiver, [Type])
tappP =
    (,) <$> (rewrapEither TyarCon TyarVar <$> conOrVarP) <*> angles appBody
    where
      appBody =
          sepBy1 typeP (symbol ",")

funP :: Parser ([Type], Type)
funP =
    do args <-
           parens $ flip sepBy (symbol ",") typeP
       _ <- symbol "=>"
       bodyT <- typeP
       pure (args, bodyT)
