module Parser.Expr where

import Parser.Literal
import Parser.Pattern
import Parser.Shared
import Types.Annotation
import Types.Ast
import Types.Common

import Data.List (foldl')
import Data.Maybe
import Text.Megaparsec hiding (Pos)
import Text.Megaparsec.Expr
import qualified Data.HashMap.Strict as HM

list :: Parser [Expr Pos]
list =
    brackets $
    flip sepBy (symbol ",") $
    exprP

ifP :: Parser (If Pos)
ifP =
    do ifHead <- branch "if"
       moreBodies <- many (branch "else if")
       elseBlock <-
           do _ <- symbol "else"
              braces exprP
       pure $ If (ifHead : moreBodies) elseBlock
    where
      branch ty =
          do _ <- symbol ty
             condE <- parens exprP
             bodyE <- braces exprP
             pure (condE, bodyE)

lambdaP :: Parser (Lambda Pos)
lambdaP =
    do args <-
           parens $ flip sepBy (symbol ",") $ posAnnotated var
       _ <- symbol "=>"
       body <- braces exprP
       pure $ Lambda args body

funAppP :: Parser (FunApp Pos)
funAppP =
    do receiver <- varOnlyExpr <|> parens exprP
       args <- parens $ flip sepBy (symbol ",") exprP
       pure $ FunApp receiver args

caseP :: Parser (Case Pos)
caseP =
    do _ <- symbol "case"
       matchOn <- parens exprP
       cases <-
           braces $
           some $
           do pat <- lexeme patternP
              _ <- symbol "->"
              expr <- exprP
              _ <- symbol ";"
              pure (pat, expr)
       pure (Case matchOn cases)

varOnlyExpr :: Parser (Expr Pos)
varOnlyExpr = EVar <$> posAnnotated var

letP :: Parser (Let Pos)
letP =
    do _ <- symbol "let"
       boundVar <- posAnnotated var
       _ <- symbol "="
       boundExpr <- exprP
       _ <- symbol ";"
       inExpr <- exprP
       pure (Let boundVar boundExpr inExpr)

mergeP :: Parser (RecordMerge Pos)
mergeP =
    braces $
    do _ <- symbol "..."
       noCopy <- isJust <$> optional (symbol "!")
       targetE <- exprP
       _ <- symbol ","
       sourcesE <-
           try simpleP <|> complexP
       pure (RecordMerge targetE sourcesE noCopy)
    where
        simpleP =
            do pos <- myPos
               kvs <-
                   flip sepBy1 (symbol ",") $
                   do key <- RecordKey <$> name
                      _ <- symbol ":"
                      val <- exprP
                      pure (key, val)
               pure [ERecord $ Annotated pos $ Record $ HM.fromList kvs]
        complexP =
            flip sepBy1 (symbol ",") $
            do _ <- symbol "..."
               exprP

accessP :: Parser (RecordAccess Pos)
accessP =
    do source <- lexeme accessLhsExprP
       _ <- symbol "."
       key <- RecordKey <$> name
       pure (RecordAccess source key)

accessExprP :: Parser (Expr Pos)
accessExprP =
    do lhs <- lexeme accessLhsExprP
       _ <- symbol "."
       path <- sepBy1 ((,) <$> (RecordKey <$> name) <*> myPos) (symbol ".")
       case path of
         [] -> fail "Internal parsing error. SepBy1 returned an empty list."
         (firstField : xs) ->
             pure $
             foldl' applyToLhs (applyToLhs lhs firstField) xs
    where
        applyToLhs lhs (field, pos) = ERecordAccess (Annotated pos (RecordAccess lhs field))

accessLhsExprP :: Parser (Expr Pos)
accessLhsExprP =
    try (EFunApp <$> posAnnotated funAppP) <|>
    try (ERecord <$> posAnnotated (record RpmNormal exprP)) <|>
    try (ERecordMerge <$> posAnnotated mergeP) <|>
    varOnlyExpr

binOpTable :: [[Operator Parser (Expr Pos)]]
binOpTable =
    [ [ prefix "!" BoNot ]
    , [ binary "*" BoMul
      , binary "/" BoDiv
      ]
    , [ binary "+" BoAdd
      , binary "-" BoSub
      ]
    , [ binary "!=" BoNeq
      , binary "==" BoEq
      ]
    , [ binary "&&" BoAnd
      , binary "||" BoOr
      ]
    ]
    where
      binary opName f =
          InfixL $
          do pos <- myPos
             _ <- symbol opName
             pure (\e1 e2 -> EBinOp (Annotated pos (f e1 e2)))
      prefix opName f =
          Prefix $
          do pos <- myPos
             _ <- symbol opName
             pure (\e1 -> EBinOp (Annotated pos (f e1)))

exprP :: Parser (Expr Pos)
exprP = makeExprParser termP binOpTable

termP :: Parser (Expr Pos)
termP =
    lexemeNl $
    try (ELet <$> posAnnotated letP) <|>
    try (ECase <$> posAnnotated caseP) <|>
    try (EIf <$> posAnnotated ifP) <|>
    try (ELit <$> posAnnotated literal) <|>
    try accessExprP <|>
    try (EList <$> posAnnotated list) <|>
    try (ERecord <$> posAnnotated (record RpmNormal exprP)) <|>
    try (ERecordMerge <$> posAnnotated mergeP) <|>
    try (ELambda <$> posAnnotated lambdaP) <|>
    try (EFunApp <$> posAnnotated funAppP) <|>
    try (parens exprP) <|>
    varOnlyExpr
