module Pretty.Expr (prettyExpr) where

import Pretty.Literal
import Pretty.Pattern
import Pretty.Shared
import Types.Ast
import Types.Common

import Data.Monoid
import qualified Data.Text as T

prettyExpr :: Expr a -> T.Text
prettyExpr e =
    case e of
      ELit (Annotated _ lit) -> prettyLiteral lit
      EVar (Annotated _ (Var x)) -> x
      EList (Annotated _ exprs) -> "[" <> T.intercalate "," (map prettyExpr exprs) <> "]"
      ERecord (Annotated _ r) -> prettyRecord r prettyExpr
      ERecordMerge (Annotated _ r) -> prettyMerge r
      EIf (Annotated _ eIf) -> prettyIf eIf
      ELet (Annotated _ eLet) -> prettyLet eLet
      ELambda (Annotated _ eLambda) -> prettyLambda eLambda
      EFunApp (Annotated _ eFunApp) -> prettyFunApp eFunApp
      ECase (Annotated _ eCase) -> prettyCase eCase

prettyIf :: If a -> T.Text
prettyIf i =
    branches <> elseBranch
    where
      branches =
          case if_bodies i of
            [] -> prettyExpr (if_else i)
            (first : rest) ->
                makeBranch "if" first <> "\n"
                <> T.intercalate "\n" (map (makeBranch "else if") rest)
      elseBranch =
          "else {"
          <> prettyExpr (if_else i) <> "}"
      makeBranch lbl (cond, body) =
          lbl <> "(" <> prettyExpr cond <> ") { " <> prettyExpr body <> "}"

prettyCase :: Case a -> T.Text
prettyCase c =
    "case" <> "(" <> prettyExpr (c_matchOn c) <> ") {\n"
    <> T.intercalate "\n" (map (uncurry handleCase) $ c_cases c)
    <> "\n}"
    where
      handleCase pat expr =
          prettyPattern pat <> " -> " <> prettyExpr expr <> ";"

prettyLet :: Let a -> T.Text
prettyLet l =
    "let " <> prettyVar (a_value (l_boundVar l)) <> " = " <> prettyExpr (l_boundExpr l) <> ";"
    <> prettyExpr (l_in l)

prettyLambda :: Lambda a -> T.Text
prettyLambda l =
    "(" <> T.intercalate ", " (map mkArg (l_args l)) <> ") => { " <> prettyExpr (l_body l) <> " }"
    where
      mkArg = prettyVar . a_value

prettyFunApp :: FunApp a -> T.Text
prettyFunApp fApp =
    "(" <> prettyExpr (fa_receiver fApp) <> ")("
    <> T.intercalate "," (map prettyExpr (fa_args fApp))
    <> ")"

prettyMerge :: RecordMerge a -> T.Text
prettyMerge rm =
    "{ \n"
    <> "..." <> prettyExpr (rm_target rm) <> ", \n"
    <> T.intercalate ", \n" (map handleE (rm_mergeIn rm))
    <> "}"
    where
      handleE e =
          "..." <> prettyExpr e
