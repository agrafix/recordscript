module Pretty.Shared where

import Types.Common

import Data.Monoid
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T

prettyRecord :: Record x -> (x -> T.Text) -> T.Text
prettyRecord (Record hm) printVal =
    "{" <> T.intercalate "," (map makePair $ HM.toList hm) <> "}"
    where
      makePair (RecordKey k, v) =
          k <> ": " <> printVal v
