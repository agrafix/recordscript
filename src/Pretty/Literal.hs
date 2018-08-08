module Pretty.Literal (prettyLiteral) where

import Types.Ast

import Data.Monoid
import Numeric
import qualified Data.Text as T

showFullPrecision :: Double -> String
showFullPrecision x = showFFloat Nothing x ""

prettyLiteral :: Literal -> T.Text
prettyLiteral l =
    case l of
      LInt i -> T.pack (show i)
      LFloat d -> T.pack (showFullPrecision d)
      LChar c -> "'" <> T.singleton c <> "'"
      LString x -> "\"" <> x <> "\"" -- TODO: fix escaping
      LBool x -> if x then "true" else "false"
