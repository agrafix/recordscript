{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Types.Ast where

import Types.Common

import Data.Data
import Data.Hashable
import GHC.Generics
import qualified Data.Text as T

newtype Var
    = Var { unVar :: T.Text }
    deriving (Eq, Ord, Show, Generic, Data, Typeable, Hashable)

data Literal
    = LInt Int
    | LFloat Double
    | LChar Char
    | LString T.Text
    | LBool Bool
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

data Pattern a
   = PVar (A a Var)
   | PLit (A a Literal)
   | PRecord (A a (Record (Pattern a)))
   | PAny a
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

data If a
    = If
    { if_bodies :: [(Expr a, Expr a)]
    , if_else :: Expr a
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

data Let a
    = Let
    { l_boundVar :: A a Var
    , l_boundExpr :: Expr a
    , l_in :: Expr a
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

data Lambda a
    = Lambda
    { l_args :: [A a Var]
    , l_body :: Expr a
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

data FunApp a
    = FunApp
    { fa_receiver :: Expr a
    , fa_args :: [Expr a]
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

data Case a
    = Case
    { c_matchOn :: Expr a
    , c_cases :: [(Pattern a, Expr a)]
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

data Expr a
    = ELit (A a Literal)
    | EVar (A a Var)
    | EList (A a [Expr a])
    | ERecord (A a (Record (Expr a)))
    | EIf (WithA a If)
    | ELet (WithA a Let)
    | ELambda (WithA a Lambda)
    | EFunApp (WithA a FunApp)
    | ECase (WithA a Case)
    deriving (Eq, Ord, Show, Generic, Data, Typeable)
