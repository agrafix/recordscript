module Test.ParserPrettySpec where

import Parser.Expr
import Parser.Literal
import Parser.Pattern
import Parser.Shared
import Parser.Types
import Pretty.Expr
import Pretty.Literal
import Pretty.Pattern
import Pretty.Types
import Types.Annotation
import Types.Ast
import Types.Common
import Types.Types

import Control.Monad
import Data.Bifunctor
import Data.Monoid
import Test.Hspec
import Text.Megaparsec (eof)
import Text.Megaparsec.Error
import qualified Data.Generics as G
import qualified Data.HashMap.Strict as HM
import qualified Data.Text as T

roundTrip :: (Eq x, Show x) => x -> (x -> T.Text) -> Parser p -> (p -> x) -> Expectation
roundTrip value pretty parse unwrap =
    do let pv = pretty value
           parseResult =
               first parseErrorPretty $
               executeParser "<test>" (parse <* eof) pv
           errorPrefix =
               "Failed to parse: \n------\n"
               ++ T.unpack pv ++ "\n------\n"
           check res =
               case res of
                 Left errMsg ->
                     expectationFailure $
                     errorPrefix ++ errMsg
                 Right parsedVal ->
                     if parsedVal /= value
                     then expectationFailure $
                          errorPrefix
                          ++ "Parsed: " ++ show parsedVal ++ "\n"
                          ++ "Expected: " ++ show value
                     else pure ()
       check $ second unwrap parseResult

literalSpec :: Spec
literalSpec =
    do it "works for ints" $ go (LInt 3)
       it "works for negative ints" $ go (LInt (-3))
       it "works for floats" $ go (LFloat 3)
       it "works for floats 2" $ go (LFloat 3.0)
       it "works for floats 3" $ go (LFloat 3.0001)
       it "works for floats 4" $ go (LFloat 0.001)
       it "works for floats 5" $ go (LFloat 110000.0001)
       it "works for negative floats" $ go (LFloat (-3))
       it "works for chars" $ go (LChar 'x')
       it "works for strings" $ go (LString "Hello from the air")
       it "works for bools" $
           do go (LBool False)
              go (LBool True)
    where
        go e = roundTrip e prettyLiteral literal id

typeSpec :: Spec
typeSpec =
    do it "works for type variabels" $
           go (Type (TVar (TypeVar "var")) SeNone)
       it "works for type constructors" $
           go (Type (TCon (TypeConstructor "Unit")) SeNone)
       it "works for type application" $
           let arg1 = TyarCon (TypeConstructor "List")
               arg2 = Type (TVar (TypeVar "a")) SeNone
           in go (Type (TApp arg1 [arg2]) SeNone)
       it "works for type application with multiple args" $
           let arg1 = TyarCon (TypeConstructor "List")
               arg2 = Type (TVar (TypeVar "a")) SeNone
               arg3 = Type (TCon (TypeConstructor "String")) SeNone
           in go (Type (TApp arg1 [arg2, arg3]) SeNone)
       it "works for open record types" $
           go $ Type (TRec $ ROpen $ Record $
           HM.fromList [(RecordKey "foo", Type (TVar (TypeVar "a")) SeNone)]) SeNone
       it "works for closed record types" $
           go $ Type (TRec $ RClosed $ Record $
           HM.fromList [(RecordKey "foo", Type (TVar (TypeVar "a")) SeNone)]) SeNone
       it "works for functions with no arguments" $
           go (Type (TFun [] (Type (TVar (TypeVar "a")) SeNone)) SeNone)
       it "works for functions" $
           let arg1 = Type (TCon (TypeConstructor "String")) SeNone
               arg2 = Type (TVar (TypeVar "a")) SeNone
               res = Type (TCon (TypeConstructor "Unit")) SeNone
           in go (Type (TFun [arg1, arg2] res) SeNone)
    where
        go e =
            roundTrip e prettyType typeP id

patternSpec :: Spec
patternSpec =
    do it "works for pattern variables" $
           go someVar
       it "works for literals" $
           go someLit
       it "works for records" $
           go someRecord
       it "works for nested records" $
           go $ PRecord $ fakeA $ Record $
           HM.fromList [(RecordKey "foo", someVar), (RecordKey "bar", someRecord)]
       it "works for any" $
           go $ PAny dummyPos
    where
        dummyPos = Pos "x" Nothing Nothing
        someRecord =
            PRecord $ fakeA $ Record $
            HM.fromList [(RecordKey "foo", someVar), (RecordKey "bar", someLit)]
        someVar = PVar $ fakeA (Var "var")
        someLit = PLit $ fakeA (LString "asf")
        clobberA :: Pattern Pos -> Pattern Pos
        clobberA e =
            let run (Pos _ _ _) = dummyPos
            in G.everywhere (G.mkT run) e
        fakeA = Annotated dummyPos
        go e =
            roundTrip e prettyPattern patternP clobberA

exprSpec :: Spec
exprSpec =
    do it "works for literals" $ go someLit
       it "works for vars" $ go someVar
       it "works for lists" $ go someList
       it "works for nested lists" $ go someNestedList
       it "works for records" $ go someRecord
       it "works for record merge that disallows copy" $ go (someMerge True)
       it "works for record merge" $ go (someMerge False)
       it "works for simple record access" $ go someRecordAccess
       it "works for nested record access" $ go someRecordAccessNested
       it "works for if" $ go someIf
       it "works for let" $ go someLet
       it "works for lambda" $ go someLambda
       it "works for fun app" $ go someFunApp
       it "works for case" $ go someCase
       forM_ (zip binOps [1..]) $ \(bo, idx :: Int) ->
           it ("works for binop " <> show idx) $ go $ someBinOp bo
       it "works for not bin op" $ go someNotBinOp
       it "works for nested bin ops" $ go someNestedBinOp
    where
        binOps =
            [BoAdd, BoSub, BoMul, BoDiv, BoEq, BoNeq, BoAnd, BoOr]
        someLit = ELit $ fakeA (LString "asd")
        someVar = EVar $ fakeA (Var "x")
        someList = EList $ fakeA [someLit, someVar]
        someNestedList = EList $ fakeA [someList, someVar]
        someRecord =
            ERecord $ fakeA $ Record $
            HM.fromList [(RecordKey "foo", someVar), (RecordKey "bar", someLit)]
        someIf =
            EIf $ fakeA If
            { if_bodies = [(someLit, someVar), (someVar, someRecord)]
            , if_else = someRecord
            }
        someLet =
            ELet $ fakeA Let
            { l_boundVar = fakeA (Var "xx")
            , l_boundExpr = someIf
            , l_in = someNestedList
            }
        someLambda =
            ELambda $ fakeA Lambda
            { l_args = [fakeA (Var "yy"), fakeA (Var "zz")]
            , l_body = someLet
            }
        someFunApp =
            EFunApp $ fakeA FunApp
            { fa_receiver = someVar
            , fa_args = [someIf, someRecord, someLet]
            }
        someCase =
            ECase $ fakeA Case
            { c_matchOn = someNestedList
            , c_cases =
                    [ (PLit $ fakeA (LString "asf"), someLambda)
                    , (PVar $ fakeA (Var "y"), someRecord)
                    ]
            }
        someMerge noCopy =
            ERecordMerge $ fakeA RecordMerge
            { rm_target = someVar
            , rm_mergeIn = [someVar, someRecord]
            , rm_noCopy = noCopy
            }
        someRecordAccess =
            ERecordAccess $ fakeA RecordAccess
            { ra_record = someRecord
            , ra_field = RecordKey "foo"
            }
        someRecordAccessNested =
            ERecordAccess $ fakeA RecordAccess
            { ra_record = someRecordAccess
            , ra_field = RecordKey "bar"
            }
        someBinOp pk =
            EBinOp $ fakeA $ pk someVar someLit
        someNotBinOp =
            EBinOp $ fakeA $ BoNot someFunApp
        someNestedBinOp =
            EBinOp $ fakeA $ BoAdd (someBinOp BoMul) (someBinOp BoSub)
        dummyPos = Pos "x" Nothing Nothing
        clobberA :: Expr Pos -> Expr Pos
        clobberA e =
            let run (Pos _ _ _) = dummyPos
            in G.everywhere (G.mkT run) e
        fakeA = Annotated dummyPos
        go e =
            roundTrip e prettyExpr exprP clobberA

parserPrettySpec :: Spec
parserPrettySpec =
    do describe "literals" literalSpec
       describe "types" typeSpec
       describe "pattern" patternSpec
       describe "expr" exprSpec
