module Parser.Expr where

import Parser.Literal
import Parser.Pattern
import Parser.Shared
import Types.Ast
import Types.Common

import Text.Megaparsec hiding (Pos)
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
       targetE <- exprP
       _ <- symbol ","
       sourcesE <-
           try simpleP <|> complexP
       pure (RecordMerge targetE sourcesE)
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

exprP :: Parser (Expr Pos)
exprP =
    lexemeNl $
    try (ELet <$> posAnnotated letP) <|>
    ECase <$> posAnnotated caseP <|>
    EIf <$> posAnnotated ifP <|>
    ELit <$> posAnnotated literal <|>
    varOnlyExpr <|>
    EList <$> posAnnotated list <|>
    try (ERecord <$> posAnnotated (record RpmNormal exprP)) <|>
    try (ERecordMerge <$> posAnnotated mergeP) <|>
    try (ELambda <$> posAnnotated lambdaP) <|>
    EFunApp <$> posAnnotated funAppP
