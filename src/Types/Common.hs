{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Types.Common where

import Data.Data
import Data.Hashable
import GHC.Generics
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T

newtype RecordKey
    = RecordKey { unRecordKey :: T.Text }
    deriving (Eq, Ord, Show, Generic, Data, Typeable, Hashable)

newtype Record v
    = Record { unRecord :: HM.HashMap RecordKey v}
    deriving (Eq, Ord, Show, Generic, Data, Typeable, Functor, Foldable, Traversable)

recordMapMaybe :: (a -> Maybe b) -> Record a -> Record b
recordMapMaybe f (Record r) =
    Record $ HM.mapMaybe f r
