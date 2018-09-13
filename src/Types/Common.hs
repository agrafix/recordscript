{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ApplicativeDo #-}
module Types.Common where

import Data.Data
import Data.Hashable
import Data.Maybe
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

recordMapMaybeM :: Applicative m => (a -> m (Maybe b)) -> Record a -> m (Record b)
recordMapMaybeM f (Record r) =
    fmap (Record . HM.fromList . catMaybes) $ traverse go $ HM.toList r
    where
      go (k, v) =
          do res <- f v
             pure $ case res of
               Nothing -> Nothing
               Just x -> Just (k, x)
