{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Types.Types where

import Types.Common

import Control.Monad
import Data.Data
import Data.Hashable
import GHC.Generics
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T

newtype TypeVar
    = TypeVar { unTypeVar :: T.Text }
    deriving (Eq, Ord, Show, Generic, Data, Typeable, Hashable)

newtype TypeConstructor
    = TypeConstructor { unTypeConstructor :: T.Text }
    deriving (Eq, Ord, Show, Generic, Data, Typeable, Hashable)

data TypeAppReceiver
    = TyarVar TypeVar
    | TyarCon TypeConstructor
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

receiverToType :: TypeAppReceiver -> TypeVal
receiverToType tar =
    case tar of
      TyarVar x -> TVar x
      TyarCon c -> TCon c

typeToReceiver :: TypeVal -> Either TypeVal TypeAppReceiver
typeToReceiver ty =
    case ty of
      TVar x -> Right (TyarVar x)
      TCon c -> Right (TyarCon c)
      _ -> Left ty

data TypeVal
    = TApp TypeAppReceiver [Type]
    -- ^ Type application
    | TVar TypeVar
    -- ^ Type variable
    | TCon TypeConstructor
    -- ^ Type constructor
    | TRec RecordType
    -- ^ Record type
    | TFun [Type] Type
    -- ^ Function type
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

data SideEffect
    = SeNone
    | SeUnknown
    | SeIo
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

data Type
    = Type
    { t_type :: TypeVal
    , t_eff :: SideEffect
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

data RecordType
    = ROpen (Record Type)
    | RClosed (Record Type)
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

mapMValueType :: Monad m => RecordType -> (Type -> m Type) -> m RecordType
mapMValueType r f =
    case r of
      ROpen rc -> ROpen <$> go rc
      RClosed rc -> RClosed <$> go rc
    where
      go (Record x) =
          Record <$>
          do kvPairs <-
                 forM (HM.toList x) $ \(k, v) ->
                 do v' <- f v
                    pure (k, v')
             pure $ HM.fromList kvPairs
