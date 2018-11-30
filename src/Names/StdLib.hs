module Names.StdLib where

import Types.Types

tInt :: Type
tInt = Type $ TCon (TypeConstructor "Int")

tFloat :: Type
tFloat = Type $ TCon (TypeConstructor "Float")

tChar :: Type
tChar = Type $ TCon (TypeConstructor "Char")

tString :: Type
tString = Type $ TCon (TypeConstructor "String")

tBool :: Type
tBool = Type $ TCon (TypeConstructor "Bool")

tList :: Type -> Type
tList x = Type $ TApp (TyarCon (TypeConstructor "List")) [x]
