module Names.StdLib where

import Types.Types

tInt :: Type
tInt = TCon (TypeConstructor "Int")

tFloat :: Type
tFloat = TCon (TypeConstructor "Float")

tChar :: Type
tChar = TCon (TypeConstructor "Char")

tString :: Type
tString = TCon (TypeConstructor "String")

tBool :: Type
tBool = TCon (TypeConstructor "Bool")

tList :: Type -> Type
tList = TApp (TCon (TypeConstructor "List"))
