module Pretty.Types where

import Types.Common
import Types.Types

import Data.Monoid
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T

prettyTypeAppRecv :: TypeAppReceiver -> T.Text
prettyTypeAppRecv tar =
    case tar of
      TyarVar (TypeVar x) -> x
      TyarCon (TypeConstructor x) -> x

prettyType :: Type -> T.Text
prettyType t =
    case t of
      TApp x y -> prettyTypeAppRecv x <> "<" <> T.intercalate "," (map prettyType y) <> ">"
      TVar (TypeVar x) -> x
      TCon (TypeConstructor x) -> x
      TRec r -> prettyRecord r
      TFun args ret ->
          "(" <> T.intercalate "," (map prettyType args) <> ") => " <> prettyType ret

prettyRecord :: RecordType -> T.Text
prettyRecord r =
    case r of
      ROpen x -> "{" <> innerRecord x <> "}"
      RClosed x -> "{|" <> innerRecord x <> "|}"

innerRecord :: Record Type -> T.Text
innerRecord (Record hm) =
    T.intercalate "," $ flip map (HM.toList hm) $ \(RecordKey k, v) ->
    k <> ": " <> prettyType v
