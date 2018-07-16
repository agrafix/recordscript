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

data Type
    = TApp Type Type
    -- ^ Type applicationve
    | TVar TypeVar
    -- ^ Type variable
    | TCon TypeConstructor
    -- ^ Type constructor
    | TRec RecordType
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

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
