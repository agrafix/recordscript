module Parser.Expr where

import Parser.Literal
import Parser.Pattern
import Parser.Shared
import Types.Ast
import Types.Common

import Text.Megaparsec hiding (Pos)

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

exprP :: Parser (Expr Pos)
exprP =
    lexemeNl $
    try (ELet <$> posAnnotated letP) <|>
    ECase <$> posAnnotated caseP <|>
    EIf <$> posAnnotated ifP <|>
    ELit <$> posAnnotated literal <|>
    varOnlyExpr <|>
    EList <$> posAnnotated list <|>
    ERecord <$> posAnnotated (record RpmNormal exprP) <|>
    try (ELambda <$> posAnnotated lambdaP) <|>
    EFunApp <$> posAnnotated funAppP
