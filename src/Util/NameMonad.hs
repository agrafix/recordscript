module Util.NameMonad
    ( runNameM
    , freshVar
    , NameM, NameMonad
    )
where

import Types.Ast

import Control.Monad.State
import Data.Functor.Identity
import Data.Monoid
import qualified Data.Text as T

data NameState
    = NameState
    { ns_varSupply :: Int
    , ns_prefix :: T.Text
    } deriving (Show, Eq, Ord)

initState :: T.Text -> NameState
initState prefix = NameState 0 prefix

freshVar :: NameM m => m Var
freshVar =
    do s <- get
       put $ s { ns_varSupply = ns_varSupply s + 1 }
       pure $ Var $ ns_prefix s <> T.pack (show (ns_varSupply s))

type NameM m = (MonadState NameState m)
type NameMonad = StateT NameState Identity

runNameM :: T.Text -> NameMonad a -> a
runNameM prefix action = runIdentity $ evalStateT action (initState prefix)
