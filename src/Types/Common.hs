{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Types.Common where

import Data.Data
import Data.Hashable
import GHC.Generics
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T

data Annotated a v
    = Annotated
    { a_ann :: a
    , a_value :: v
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

instance Functor (Annotated a) where
    fmap f (Annotated a v) = Annotated a (f v)

mapMA :: Functor m => (a -> m b) -> Annotated x a -> m (Annotated x b)
mapMA f (Annotated ann val) =
    Annotated ann <$> f val

type A a v = Annotated a v
type WithA a v = A a (v a)


newtype RecordKey
    = RecordKey { unRecordKey :: T.Text }
    deriving (Eq, Ord, Show, Generic, Data, Typeable, Hashable)

newtype Record v
    = Record { unRecord :: HM.HashMap RecordKey v}
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

data Pos
    = Pos
    { p_file :: T.Text
    , p_line :: Maybe Int
    , p_column :: Maybe Int
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)
