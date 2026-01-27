{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Basic
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram
import Strat.Poly.Graph (EdgeId(..), validateDiagram, unionDisjointIntMap)


tests :: TestTree
tests =
  testGroup
    "Poly.Basic"
    [ testCase "diagram dom/cod" testDiagramDomCod
    , testCase "compD rejects boundary mismatch" testCompMismatch
    , testCase "tensorD rejects mode mismatch" testTensorModeMismatch
    , testCase "validateDiagram detects stale incidence" testValidateStaleIncidence
    , testCase "unionDisjointIntMap rejects collisions" testUnionDisjoint
    ]


testDiagramDomCod :: Assertion
testDiagramDomCod = do
  let mode = ModeName "Cart"
  let a = TCon (TypeName "A") []
  let ctx = [a]
  case genD mode ctx ctx (GenName "f") of
    Left err -> assertFailure (T.unpack err)
    Right diag -> do
      dom <- case diagramDom diag of
        Left err -> assertFailure (T.unpack err)
        Right d -> pure d
      cod <- case diagramCod diag of
        Left err -> assertFailure (T.unpack err)
        Right d -> pure d
      dom @?= ctx
      cod @?= ctx


testCompMismatch :: Assertion
testCompMismatch = do
  let mode = ModeName "Cart"
  let a = TCon (TypeName "A") []
  let b = TCon (TypeName "B") []
  let g = idD mode [a]
  let f = idD mode [b]
  case compD g f of
    Left _ -> pure ()
    Right _ -> assertFailure "expected boundary mismatch"


testTensorModeMismatch :: Assertion
testTensorModeMismatch = do
  let modeA = ModeName "A"
  let modeB = ModeName "B"
  let a = TCon (TypeName "A") []
  let d1 = idD modeA [a]
  let d2 = idD modeB [a]
  case tensorD d1 d2 of
    Left _ -> pure ()
    Right _ -> assertFailure "expected mode mismatch"

testValidateStaleIncidence :: Assertion
testValidateStaleIncidence = do
  let mode = ModeName "Cart"
  let a = TCon (TypeName "A") []
  diag <- case genD mode [a] [a] (GenName "f") of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let bad = diag { dProd = IM.insert 0 (Just (EdgeId 99)) (dProd diag) }
  case validateDiagram bad of
    Left _ -> pure ()
    Right _ -> assertFailure "expected validation failure for stale incidence"

testUnionDisjoint :: Assertion
testUnionDisjoint = do
  let left = IM.fromList [(0 :: Int, "a")]
  let right = IM.fromList [(0 :: Int, "b")]
  case unionDisjointIntMap "test" left right of
    Left _ -> pure ()
    Right _ -> assertFailure "expected union collision error"
