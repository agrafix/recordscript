module Pretty.Pattern (prettyPattern) where

import Pretty.Literal
import Pretty.Shared
import Types.Ast
import Types.Common

import qualified Data.Text as T

prettyPattern :: Pattern a -> T.Text
prettyPattern p =
    case p of
      PVar (Annotated _ (Var x)) -> x
      PLit (Annotated _ lit) -> prettyLiteral lit
      PRecord (Annotated _ r) -> prettyRecord r prettyPattern
      PAny _ -> "_"
