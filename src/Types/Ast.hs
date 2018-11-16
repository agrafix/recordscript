{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Types.Ast where

import Types.Annotation
import Types.Common
import Types.Types
import qualified Data.HashMap.Strict as HM

import Data.Bifunctor
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

mapPatAnn :: (a -> b) -> Pattern a -> Pattern b
mapPatAnn f pat =
    case pat of
      PVar (Annotated x v) -> PVar (Annotated (f x) v)
      PLit (Annotated x l) -> PLit (Annotated (f x) l)
      PAny x -> PAny (f x)
      PRecord (Annotated x (Record hm)) ->
          PRecord $ Annotated (f x) $ Record $ HM.map (mapPatAnn f) hm

data If a
    = If
    { if_bodies :: [(Expr a, Expr a)]
    , if_else :: Expr a
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

ifTransform :: (Expr a -> Expr b) -> If a -> If b
ifTransform f i =
    If
    { if_bodies = map (bimap f f) (if_bodies i)
    , if_else = f (if_else i)
    }

ifTransformM :: Monad m => (Expr a -> m (Expr b)) -> If a -> m (If b)
ifTransformM f i =
    mapM (\(a, b) -> (,) <$> f a <*> f b) (if_bodies i) >>= \bodies ->
    f (if_else i) >>= \elseE ->
    pure If
    { if_bodies = bodies
    , if_else = elseE
    }

ifApplyM :: Monad m => (Expr a -> m ()) -> If a -> m ()
ifApplyM f i =
    do mapM_ (\(a, b) -> (,) <$> f a <*> f b) (if_bodies i)
       f (if_else i)

data Let a
    = Let
    { l_boundVar :: A a Var
    , l_boundExpr :: Expr a
    , l_in :: Expr a
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

letTransform' :: (Expr a -> Expr b) -> (a -> b) -> Let a -> Let b
letTransform' f g (Let boundVar boundExpr inE) =
    Let
    { l_boundVar =
            Annotated (g (a_ann boundVar)) (a_value boundVar)
    , l_boundExpr = f boundExpr
    , l_in = f inE
    }

data Lambda a
    = Lambda
    { l_args :: [A a Var]
    , l_body :: Expr a
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

lambdaTransform' :: (Expr a -> Expr b) -> (a -> b) -> Lambda a -> Lambda b
lambdaTransform' f g (Lambda args body) =
    Lambda
    { l_args = map (\x -> Annotated (g (a_ann x)) (a_value x)) args
    , l_body = f body
    }

data FunApp a
    = FunApp
    { fa_receiver :: Expr a
    , fa_args :: [Expr a]
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

funAppTransform :: (Expr a -> Expr b) -> FunApp a -> FunApp b
funAppTransform f fa =
    FunApp
    { fa_receiver = f (fa_receiver fa)
    , fa_args = fmap f (fa_args fa)
    }

funAppTransformM :: (Monad m) => (Expr a -> m (Expr b)) -> FunApp a -> m (FunApp b)
funAppTransformM f fa =
    f (fa_receiver fa) >>= \recv ->
    mapM f (fa_args fa) >>= \args ->
    pure FunApp
    { fa_receiver = recv
    , fa_args = args
    }

funAppApplyM :: (Monad m) => (Expr a -> m ()) -> FunApp a -> m ()
funAppApplyM f fa =
    do f (fa_receiver fa)
       mapM_ f (fa_args fa)

data Case a
    = Case
    { c_matchOn :: Expr a
    , c_cases :: [(Pattern a, Expr a)]
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

caseTransform :: (Expr a -> Expr a) -> Case a -> Case a
caseTransform f i =
    Case
    { c_cases = map (second f) (c_cases i)
    , c_matchOn = f (c_matchOn i)
    }

caseTransform' :: (Expr a -> Expr b) -> (Pattern a -> Pattern b) -> Case a -> Case b
caseTransform' f g i =
    Case
    { c_cases = map (first g . second f) (c_cases i)
    , c_matchOn = f (c_matchOn i)
    }

caseTransformM :: Monad m => (Expr a -> m (Expr a)) -> Case a -> m (Case a)
caseTransformM f i =
    Case <$> f (c_matchOn i) <*> mapM (\(a, b) -> (,) <$> pure a <*> f b) (c_cases i)

caseApplyM :: Monad m => (Expr a -> m ()) -> Case a -> m ()
caseApplyM f i =
    do f (c_matchOn i)
       mapM_ (\(a, b) -> (,) <$> pure a <*> f b) (c_cases i)

data RecordMerge a
    = RecordMerge
    { rm_target :: Expr a
    , rm_mergeIn :: [Expr a]
    , rm_noCopy :: Bool
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

recordMergeTransform :: (Expr a -> Expr b) -> RecordMerge a -> RecordMerge b
recordMergeTransform f rm =
    RecordMerge
    { rm_target = f (rm_target rm)
    , rm_mergeIn = fmap f (rm_mergeIn rm)
    , rm_noCopy = rm_noCopy rm
    }

recordMergeTransformM :: Monad m => (Expr a -> m (Expr b)) -> RecordMerge a -> m (RecordMerge b)
recordMergeTransformM f rm =
    f (rm_target rm) >>= \tgt ->
    mapM f (rm_mergeIn rm) >>= \mergeIn ->
    pure
    RecordMerge
    { rm_target = tgt
    , rm_mergeIn = mergeIn
    , rm_noCopy = rm_noCopy rm
    }

recordMergeApplyM :: Monad m => (Expr a -> m ()) -> RecordMerge a -> m ()
recordMergeApplyM f rm =
    do f (rm_target rm)
       mapM_ f (rm_mergeIn rm)

data RecordAccess a
    = RecordAccess
    { ra_record :: Expr a
    , ra_field :: RecordKey
    } deriving (Eq, Ord, Show, Generic, Data, Typeable)

recordAccessTransform :: (Expr a -> Expr b) -> RecordAccess a -> RecordAccess b
recordAccessTransform f ra =
    RecordAccess
    { ra_record = f (ra_record ra)
    , ra_field = ra_field ra
    }

recordAccessTransformM :: Monad m => (Expr a -> m (Expr b)) -> RecordAccess a -> m (RecordAccess b)
recordAccessTransformM f ra =
    f (ra_record ra) >>= \record ->
    pure RecordAccess
    { ra_record = record
    , ra_field = ra_field ra
    }

recordAccessApplyM :: Monad m => (Expr a -> m ()) -> RecordAccess a -> m ()
recordAccessApplyM f ra =
    f (ra_record ra)

data BinOp a
    = BoAdd (Expr a) (Expr a)
    | BoSub (Expr a) (Expr a)
    | BoMul (Expr a) (Expr a)
    | BoDiv (Expr a) (Expr a)
    | BoEq (Expr a) (Expr a)
    | BoNeq (Expr a) (Expr a)
    | BoAnd (Expr a) (Expr a)
    | BoOr (Expr a) (Expr a)
    | BoGt (Expr a) (Expr a)
    | BoLt (Expr a) (Expr a)
    | BoGtEq (Expr a) (Expr a)
    | BoLtEq (Expr a) (Expr a)
    | BoNot (Expr a)
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

binOpTransform :: (Expr a -> Expr b) -> BinOp a -> BinOp b
binOpTransform f bo =
    case bo of
      BoAdd a b -> BoAdd (f a) (f b)
      BoSub a b -> BoSub (f a) (f b)
      BoMul a b -> BoMul (f a) (f b)
      BoDiv a b -> BoDiv (f a) (f b)
      BoEq a b -> BoEq (f a) (f b)
      BoNeq a b -> BoNeq (f a) (f b)
      BoAnd a b -> BoAnd (f a) (f b)
      BoOr a b -> BoOr (f a) (f b)
      BoGt a b -> BoGt (f a) (f b)
      BoLt a b -> BoLt (f a) (f b)
      BoGtEq a b -> BoGtEq (f a) (f b)
      BoLtEq a b -> BoLtEq (f a) (f b)
      BoNot x -> BoNot (f x)

binOpTransformM :: Monad m => (Expr a -> m (Expr b)) -> BinOp a -> m (BinOp b)
binOpTransformM f bo =
    case bo of
      BoAdd a b -> BoAdd <$> f a <*> f b
      BoSub a b -> BoSub <$> f a <*> f b
      BoMul a b -> BoMul <$> f a <*> f b
      BoDiv a b -> BoDiv <$> f a <*> f b
      BoEq a b -> BoEq <$> f a <*> f b
      BoOr a b -> BoOr <$> f a <*> f b
      BoGt a b -> BoGt <$> f a <*> f b
      BoLt a b -> BoLt <$> f a <*> f b
      BoNeq a b -> BoNeq <$> f a <*> f b
      BoAnd a b -> BoAnd <$> f a <*> f b
      BoGtEq a b -> BoGtEq <$> f a <*> f b
      BoLtEq a b -> BoLtEq <$> f a <*> f b
      BoNot x -> BoNot <$> f x

binOpApplyM :: Monad m => (Expr a -> m ()) -> BinOp a -> m ()
binOpApplyM f bo =
    case bo of
      BoAdd a b -> f a >> f b
      BoSub a b -> f a >> f b
      BoMul a b -> f a >> f b
      BoDiv a b -> f a >> f b
      BoEq a b -> f a >> f b
      BoOr a b -> f a >> f b
      BoGt a b -> f a >> f b
      BoLt a b -> f a >> f b
      BoNeq a b -> f a >> f b
      BoAnd a b -> f a >> f b
      BoGtEq a b -> f a >> f b
      BoLtEq a b -> f a >> f b
      BoNot x -> f x

data Expr a
    = ELit (A a Literal)
    | EVar (A a Var)
    | EList (A a [Expr a])
    | ERecord (A a (Record (Expr a)))
    | ERecordMerge (WithA a RecordMerge)
    | ERecordAccess (WithA a RecordAccess)
    | EIf (WithA a If)
    | ELet (WithA a Let)
    | ELambda (WithA a Lambda)
    | EFunApp (WithA a FunApp)
    | ECase (WithA a Case)
    | EBinOp (WithA a BinOp)
    | ECopy (Expr a)
    deriving (Eq, Ord, Show, Generic, Data, Typeable)

isLit :: Literal -> Expr a -> Bool
isLit l expr =
    case expr of
      ELit (Annotated _ r) -> r == l
      _ -> False

isLambda :: Expr a -> Bool
isLambda expr =
    case expr of
      ELambda _ -> True
      _ -> False

toRecord :: Expr a -> Maybe (Record (Expr a))
toRecord expr =
    case expr of
      ERecord (Annotated _ r) -> Just r
      _ -> Nothing

toVar :: Expr a -> Maybe Var
toVar expr =
    case expr of
      EVar (Annotated _ l) -> Just l
      _ -> Nothing

toLambda :: Expr a -> Maybe (Lambda a)
toLambda expr =
    case expr of
      ELambda (Annotated _ l) -> Just l
      _ -> Nothing

toLiteral :: Expr a -> Maybe Literal
toLiteral expr =
    case expr of
      ELit (Annotated _ l) -> Just l
      _ -> Nothing

isLiteral :: Expr a -> Bool
isLiteral expr =
    case expr of
      ELit _ -> True
      _ -> False

isBool :: Bool -> Expr a -> Bool
isBool x = isLit (LBool x)

getExprAnn :: Expr a -> a
getExprAnn expr =
    case expr of
      ELit (Annotated x _) -> x
      EVar (Annotated x _) -> x
      EList (Annotated x _) -> x
      ERecord (Annotated x _) -> x
      ERecordMerge (Annotated x _) -> x
      ERecordAccess (Annotated x _) -> x
      EIf (Annotated x _) -> x
      ELet (Annotated x _) -> x
      ELambda (Annotated x _) -> x
      EFunApp (Annotated x _) -> x
      ECase (Annotated x _) -> x
      EBinOp (Annotated x _) -> x
      ECopy e -> getExprAnn e

getExprType :: Expr TypedPos -> Type
getExprType = tp_type . getExprAnn

mapAnn :: (a -> b) -> Expr a -> Expr b
mapAnn f expr =
    case expr of
      ELit (Annotated x l) -> ELit (Annotated (f x) l)
      EVar (Annotated x v) -> EVar (Annotated (f x) v)
      EList (Annotated x els) -> EList (Annotated (f x) $ map (mapAnn f) els)
      ERecord (Annotated x (Record r)) ->
          ERecord (Annotated (f x) $ Record $ HM.map (mapAnn f) r)
      ERecordMerge (Annotated x rm) ->
          ERecordMerge $ Annotated (f x) $ recordMergeTransform (mapAnn f) rm
      ERecordAccess (Annotated x ra) ->
          ERecordAccess $ Annotated (f x) $ recordAccessTransform (mapAnn f) ra
      EIf (Annotated x ifE) ->
          EIf $ Annotated (f x) $ ifTransform (mapAnn f) ifE
      ELet (Annotated x letE) ->
          ELet $ Annotated (f x ) $ letTransform' (mapAnn f) f letE
      ELambda (Annotated x la) ->
          ELambda $ Annotated (f x) $ lambdaTransform' (mapAnn f) f la
      EFunApp (Annotated x fa) ->
          EFunApp $ Annotated (f x) $ funAppTransform (mapAnn f) fa
      ECase (Annotated x caseE) ->
          ECase $ Annotated (f x) $ caseTransform' (mapAnn f) (mapPatAnn f) caseE
      EBinOp (Annotated x binOpE) ->
          EBinOp $ Annotated (f x) $ binOpTransform (mapAnn f) binOpE
      ECopy e -> ECopy $ mapAnn f e
