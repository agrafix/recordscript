{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Types.Annotation where

import Types.Types

import Data.Data
import Data.Monoid
import GHC.Generics
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

data Pos
    = Pos
    { p_file :: T.Text
    , p_line :: Maybe Int
    , p_column :: Maybe Int
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

prettyPos :: Pos -> T.Text
prettyPos p =
    p_file p <> "@"
    <> (maybe "?" (T.pack . show) (p_line p))
    <> ":"
    <> (maybe "?" (T.pack . show) (p_column p))

data TypedPos
    = TypedPos
    { tp_pos :: Pos
    , tp_type :: Type
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

unknownPos :: Pos
unknownPos =
    Pos
    { p_file = "<unknown>"
    , p_line = Nothing
    , p_column = Nothing
    }
