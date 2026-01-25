{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Basic
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.Syntax (OpName(..))
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.TypeExpr (TypeExpr(..))
import Strat.Poly.Diagram
import Strat.Poly.Eval (evalDiagram)
import Test.Kernel.Fixtures (sigBasic, objSort)


tests :: TestTree
tests =
  testGroup
    "Poly.Basic"
    [ testCase "diagram dom/cod" testDiagramDomCod
    , testCase "compD rejects boundary mismatch" testCompMismatch
    , testCase "tensorD rejects mode mismatch" testTensorModeMismatch
    , testCase "eval detects id boundary mismatch" testEvalIdBoundaryMismatch
    ]


testDiagramDomCod :: Assertion
testDiagramDomCod = do
  let mode = ModeName "Cart"
  let a = TySort objSort
  let ctx = [a]
  let diag = genD mode ctx ctx (GLUser (OpName "f"))
  diagramDom diag @?= ctx
  diagramCod diag @?= ctx


testCompMismatch :: Assertion
testCompMismatch = do
  let mode = ModeName "Cart"
  let a = TySort objSort
  let ctx1 = [a]
  let ctx2 = [a, a]
  let g = genD mode ctx1 ctx1 (GLUser (OpName "f"))
  let f = idD mode ctx2
  case compD g f of
    Left _ -> pure ()
    Right _ -> assertFailure "expected boundary mismatch"


testTensorModeMismatch :: Assertion
testTensorModeMismatch = do
  let modeA = ModeName "A"
  let modeB = ModeName "B"
  let a = TySort objSort
  let d1 = idD modeA [a]
  let d2 = idD modeB [a]
  case tensorD d1 d2 of
    Left _ -> pure ()
    Right _ -> assertFailure "expected mode mismatch"

testEvalIdBoundaryMismatch :: Assertion
testEvalIdBoundaryMismatch = do
  let mode = ModeName "Cart"
  let a = TySort objSort
  let diag = idD mode [a]
  case evalDiagram sigBasic [] diag of
    Left _ -> pure ()
    Right _ -> assertFailure "expected boundary mismatch"
