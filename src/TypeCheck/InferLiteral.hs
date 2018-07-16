module TypeCheck.InferLiteral where

import Types.Ast
import Types.Types
import qualified Names.StdLib as N

inferLiteral :: Literal -> Type
inferLiteral x =
    case x of
      LInt _ -> N.tInt
      LFloat _ -> N.tFloat
      LChar _ -> N.tChar
      LString _ -> N.tString
      LBool _ -> N.tBool
