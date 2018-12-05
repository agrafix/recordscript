module Names.StdLib where

import Types.Types

tInt :: Type
tInt = Type (TCon (TypeConstructor "Int")) SeNone

tFloat :: Type
tFloat = Type (TCon (TypeConstructor "Float")) SeNone

tChar :: Type
tChar = Type (TCon (TypeConstructor "Char")) SeNone

tString :: Type
tString = Type (TCon (TypeConstructor "String")) SeNone

tBool :: Type
tBool = Type (TCon (TypeConstructor "Bool")) SeNone

tVoid :: Type
tVoid = Type (TCon (TypeConstructor "Void")) SeNone

tList :: Type -> Type
tList x = Type (TApp (TyarCon (TypeConstructor "List")) [x]) SeNone
