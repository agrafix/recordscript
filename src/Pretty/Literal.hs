module Pretty.Literal where

import Types.Ast

import Data.Monoid
import qualified Data.Text as T

prettyLiteral :: Literal -> T.Text
prettyLiteral l =
    case l of
      LInt i -> T.pack (show i)
      LFloat d -> T.pack (show d)
      LChar c -> "'" <> T.singleton c <> "'"
      LString x -> "\"" <> x <> "\"" -- TODO: fix escaping
      LBool x -> if x then "true" else "false"
