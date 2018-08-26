{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Types.CopyKinds where

import Types.Common

import Data.Data
import Data.Hashable
import GHC.Generics
import qualified Data.Text as T

data CopyRestriction
    = CrNoCopy
    | CrAvoidCopy
    | CrDontCare
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

newtype CopyVar
    = CopyVar { unCopyVar :: T.Text }
    deriving (Eq, Ord, Show, Generic, Data, Typeable, Hashable)

data CopyKind
    = CkVar CopyVar
    | CkRec CopyRestriction CopyRecordKind
    | CkExplicit CopyRestriction
    | CkFun [CopyKind] CopyKind
    | CkApp CopyKind [CopyKind]
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

newtype CopyRecordKind
    = CopyRecordKind { unCopyRecordKind :: Record CopyKind }
    deriving (Eq, Ord, Show, Generic, Data, Typeable)
