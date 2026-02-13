{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.DiagramUnion
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.Poly.Diagram (unionDiagram)
import Strat.Poly.Graph
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..))


tests :: TestTree
tests =
  testGroup
    "Poly.DiagramUnion"
    [ testCase "unionDiagram uses max next ids" testUnionDiagramUsesMaxNextIds
    , testCase "deleteEdgeKeepPorts clears incidence entries" testDeleteEdgeClearsIncidence
    , testCase "deletePortIfDangling enforces incidence precondition" testDeletePortIfDangling
    ]

modeName :: ModeName
modeName = ModeName "M"

aTy :: TypeExpr
aTy = TCon (TypeRef modeName (TypeName "A")) []

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

mkSingleEdgeDiagram :: Either Text Diagram
mkSingleEdgeDiagram = do
  let (pIn, d0) = freshPort aTy (emptyDiagram modeName [])
  let (pOut, d1) = freshPort aTy d0
  d2 <- addEdge (GenName "f") [pIn] [pOut] d1
  let d3 = d2 { dIn = [pIn], dOut = [pOut] }
  validateDiagram d3
  pure d3

testUnionDiagramUsesMaxNextIds :: Assertion
testUnionDiagramUsesMaxNextIds = do
  base <- require mkSingleEdgeDiagram
  let left = shiftDiagram 100 50 base
  let right = shiftDiagram 1 3 base
  merged <- require (unionDiagram left right)
  dNextPort merged @?= max (dNextPort left) (dNextPort right)
  dNextEdge merged @?= max (dNextEdge left) (dNextEdge right)
  let ports = S.fromList (diagramPortIds merged)
  assertBool "expected shifted-left port in union" (PortId 100 `S.member` ports)
  assertBool "expected shifted-right port in union" (PortId 1 `S.member` ports)
  let next = dNextPort merged
  let (fresh, _) = freshPort aTy merged
  fresh @?= PortId next
  assertBool "fresh port id should be new" (fresh `S.notMember` ports)

testDeleteEdgeClearsIncidence :: Assertion
testDeleteEdgeClearsIncidence = do
  diag <- require mkSingleEdgeDiagram
  let [pIn] = dIn diag
  let [pOut] = dOut diag
  diag' <- require (deleteEdgeKeepPorts diag (EdgeId 0))
  assertBool "edge should be deleted" (IM.notMember 0 (dEdges diag'))
  IM.lookup (unPortId pIn) (dCons diag') @?= Just Nothing
  IM.lookup (unPortId pOut) (dProd diag') @?= Just Nothing

testDeletePortIfDangling :: Assertion
testDeletePortIfDangling = do
  diag <- require mkSingleEdgeDiagram
  let [pIn] = dIn diag
  let [pOut] = dOut diag
  case deletePortIfDangling diag pIn of
    Left _ -> pure ()
    Right _ -> assertFailure "expected deleting non-dangling port to fail"
  noEdge <- require (deleteEdgeKeepPorts diag (EdgeId 0))
  pruned <- require (deletePortIfDangling noEdge pIn)
  assertBool "deleted port should be removed from type table" (IM.notMember (unPortId pIn) (dPortTy pruned))
  assertBool "deleted port should be removed from boundary" (pIn `notElem` dIn pruned)
  empty <- require (deletePortsIfDangling noEdge [pIn, pOut])
  diagramPortIds empty @?= []
  require (validateDiagram empty)
