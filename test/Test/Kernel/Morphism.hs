{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.Morphism
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.DSL.Parse (parseRawFile)
import Strat.Kernel.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (ModuleEnv(..))
import qualified Data.Map.Strict as M
import qualified Data.Text as T


tests :: TestTree
tests =
  testGroup
    "Kernel.Morphism"
    [ testCase "morphism check uses fuel (undecided fails)" testMorphismFuelUndecided
    , testCase "morphism check succeeds with fuel" testMorphismFuelOk
    , testCase "op->term morphism preserves equation" testMorphismOpTermOk
    , testCase "op->term morphism fails obligation" testMorphismOpTermFail
    , testCase "op mapping with vars requires params" testMorphismParamRequired
    ]


testMorphismFuelUndecided :: Assertion
testMorphismFuelUndecided = do
  let src = T.unlines
        [ "doctrine I where {"
        , "  sort Obj;"
        , "  op a : Obj;"
        , "  op f : (x:Obj) -> Obj;"
        , "  computational r : (x:Obj) |- f(?x) -> ?x;"
        , "}"
        , "doctrine D where {"
        , "  sort Obj;"
        , "  op a : Obj;"
        , "  op f : (x:Obj) -> Obj;"
        , "  computational r : (x:Obj) |- f(?x) -> ?x;"
        , "}"
        , "morphism M : I -> D where {"
        , "  sort Obj = Obj;"
        , "  op a = a;"
        , "  op f = f;"
        , "} check { fuel 0; };"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertBool "expected undecided morphism error" ("MorphismEqUndecided" `T.isInfixOf` err)
        Right _ -> assertFailure "expected morphism check failure"


testMorphismFuelOk :: Assertion
testMorphismFuelOk = do
  let src = T.unlines
        [ "doctrine I where {"
        , "  sort Obj;"
        , "  op a : Obj;"
        , "  op f : (x:Obj) -> Obj;"
        , "  computational r : (x:Obj) |- f(?x) -> ?x;"
        , "}"
        , "doctrine D where {"
        , "  sort Obj;"
        , "  op a : Obj;"
        , "  op f : (x:Obj) -> Obj;"
        , "  computational r : (x:Obj) |- f(?x) -> ?x;"
        , "}"
        , "morphism M : I -> D where {"
        , "  sort Obj = Obj;"
        , "  op a = a;"
        , "  op f = f;"
        , "} check { fuel 1; };"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right env ->
          case M.lookup "M" (meMorphisms env) of
            Nothing -> assertFailure "missing morphism"
            Just _ -> pure ()

testMorphismOpTermOk :: Assertion
testMorphismOpTermOk = do
  let src = T.unlines
        [ "doctrine Invol where {"
        , "  sort Obj;"
        , "  op f : (x:Obj) -> Obj;"
        , "  computational inv : (x:Obj) |- f(f(?x)) -> ?x;"
        , "}"
        , "doctrine Invol2 where {"
        , "  sort Obj;"
        , "  op g : (x:Obj) -> Obj;"
        , "  computational inv : (x:Obj) |- g(g(?x)) -> ?x;"
        , "}"
        , "morphism Double : Invol -> Invol2 where {"
        , "  sort Obj = Obj;"
        , "  op f(x) = g(g(?x));"
        , "} check { fuel 10; };"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err)
        Right env ->
          case M.lookup "Double" (meMorphisms env) of
            Nothing -> assertFailure "missing morphism"
            Just _ -> pure ()

testMorphismOpTermFail :: Assertion
testMorphismOpTermFail = do
  let src = T.unlines
        [ "doctrine Invol where {"
        , "  sort Obj;"
        , "  op f : (x:Obj) -> Obj;"
        , "  computational inv : (x:Obj) |- f(f(?x)) -> ?x;"
        , "}"
        , "doctrine Plain where {"
        , "  sort Obj;"
        , "  op g : (x:Obj) -> Obj;"
        , "}"
        , "morphism Bad : Invol -> Plain where {"
        , "  sort Obj = Obj;"
        , "  op f(x) = g(?x);"
        , "} check { fuel 5; };"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left _ -> pure ()
        Right _ -> assertFailure "expected morphism check failure"

testMorphismParamRequired :: Assertion
testMorphismParamRequired = do
  let src = T.unlines
        [ "doctrine A where {"
        , "  sort Obj;"
        , "  op f : (x:Obj) -> Obj;"
        , "}"
        , "doctrine B where {"
        , "  sort Obj;"
        , "  op g : (x:Obj) -> Obj;"
        , "}"
        , "morphism M : A -> B where {"
        , "  sort Obj = Obj;"
        , "  op f = g(?x);"
        , "}"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err)
    Right rf ->
      case elabRawFile rf of
        Left _ -> pure ()
        Right _ -> assertFailure "expected parameter requirement error"
