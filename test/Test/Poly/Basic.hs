{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Basic
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TyVar(..))
import Strat.Poly.UnifyTy (applySubstTy, normalizeSubst)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Names (BoxName(..))
import Strat.Poly.Diagram
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), validateDoctrine)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Kernel.Types (RuleClass(..), Orientation(..))
import Strat.Poly.Surface.SSA (elabSSA)
import Strat.Poly.Graph
  ( Diagram(..)
  , EdgeId(..)
  , PortId(..)
  , Edge(..)
  , EdgePayload(..)
  , emptyDiagram
  , freshPort
  , addEdgePayload
  , validateDiagram
  , unionDisjointIntMap
  , diagramIsoEq
  )


tests :: TestTree
tests =
  testGroup
    "Poly.Basic"
    [ testCase "diagram dom/cod" testDiagramDomCod
    , testCase "compD rejects boundary mismatch" testCompMismatch
    , testCase "tensorD rejects mode mismatch" testTensorModeMismatch
    , testCase "validateDiagram detects stale incidence" testValidateStaleIncidence
    , testCase "validateDiagram detects missing output boundary" testValidateMissingOutputBoundary
    , testCase "validateDiagram detects unused input" testValidateUnusedInput
    , testCase "validateDiagram detects duplicate outputs" testValidateDuplicateOutputs
    , testCase "diagram iso equality ignores ids" testDiagramIsoEq
    , testCase "ssa rejects swapped output order" testSSASwappedOut
    , testCase "unionDisjointIntMap rejects collisions" testUnionDisjoint
    , testCase "applySubstTy chases substitutions" testApplySubstChase
    , testCase "applySubstTy handles cycles" testApplySubstCycle
    , testCase "normalizeSubst drops identity" testNormalizeSubstIdentity
    , testCase "diagram iso ignores box names" testDiagramIsoBoxName
    , testCase "validateDoctrine rejects duplicate gen tyvars" testDuplicateGenTyVars
    , testCase "validateDoctrine rejects duplicate cell tyvars" testDuplicateCellTyVars
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure


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

testValidateMissingOutputBoundary :: Assertion
testValidateMissingOutputBoundary = do
  let mode = ModeName "Cart"
  let a = TCon (TypeName "A") []
  diag <- case genD mode [a] [a] (GenName "f") of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let bad = diag { dOut = [] }
  case validateDiagram bad of
    Left _ -> pure ()
    Right _ -> assertFailure "expected validation failure for missing output boundary"

testValidateUnusedInput :: Assertion
testValidateUnusedInput = do
  let mode = ModeName "Cart"
  let a = TCon (TypeName "A") []
  let diag = idD mode [a]
  let bad = diag { dOut = [] }
  case validateDiagram bad of
    Left _ -> pure ()
    Right _ -> assertFailure "expected validation failure for unused input"

testValidateDuplicateOutputs :: Assertion
testValidateDuplicateOutputs = do
  let mode = ModeName "Cart"
  let a = TCon (TypeName "A") []
  let diag = idD mode [a]
  case dOut diag of
    [p] -> do
      let bad = diag { dOut = [p, p] }
      case validateDiagram bad of
        Left _ -> pure ()
        Right _ -> assertFailure "expected validation failure for duplicate outputs"
    _ -> assertFailure "unexpected boundary shape"

testDiagramIsoEq :: Assertion
testDiagramIsoEq = do
  let mode = ModeName "Cart"
  let a = TCon (TypeName "A") []
  diag <- case buildIsoDiagram mode a of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  diag' <- case permuteIsoDiagram diag of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  case diagramIsoEq diag diag' of
    Left err -> assertFailure (T.unpack err)
    Right ok ->
      if ok then pure () else assertFailure "expected diagrams to be iso-equivalent"

testSSASwappedOut :: Assertion
testSSASwappedOut = do
  let mode = ModeName "M"
  let a = TCon (TypeName "A") []
  let doc = Doctrine
        { dName = "SSA"
        , dModes = ModeTheory (S.singleton mode) M.empty []
        , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", 0)])]
        , dGens = M.empty
        , dCells2 = []
        }
  let program = T.unlines
        [ "diag {"
        , "  in x:A, y:A;"
        , "  out y, x;"
        , "}"
        ]
  case elabSSA doc mode program of
    Left _ -> pure ()
    Right _ -> assertFailure "expected SSA to reject swapped output order"

testUnionDisjoint :: Assertion
testUnionDisjoint = do
  let left = IM.fromList [(0 :: Int, "a")]
  let right = IM.fromList [(0 :: Int, "b")]
  case unionDisjointIntMap "test" left right of
    Left _ -> pure ()
    Right _ -> assertFailure "expected union collision error"

testApplySubstChase :: Assertion
testApplySubstChase = do
  let a = TyVar "a"
  let b = TyVar "b"
  let c = TCon (TypeName "C") []
  let subst = M.fromList [(a, TVar b), (b, c)]
  applySubstTy subst (TVar a) @?= c

testApplySubstCycle :: Assertion
testApplySubstCycle = do
  let a = TyVar "a"
  let b = TyVar "b"
  let subst = M.fromList [(a, TVar b), (b, TVar a)]
  applySubstTy subst (TVar a) @?= TVar a

testNormalizeSubstIdentity :: Assertion
testNormalizeSubstIdentity = do
  let a = TyVar "a"
  normalizeSubst (M.fromList [(a, TVar a)]) @?= M.empty

testDiagramIsoBoxName :: Assertion
testDiagramIsoBoxName = do
  let mode = ModeName "M"
  let a = TCon (TypeName "A") []
  let inner = idD mode [a]
  let (inP, d0) = freshPort a (emptyDiagram mode)
  let (outP, d1) = freshPort a d0
  d2 <- require (addEdgePayload (PBox (BoxName "B1") inner) [inP] [outP] d1)
  let d3 = d2 { dIn = [inP], dOut = [outP] }
  d4 <- require (addEdgePayload (PBox (BoxName "B2") inner) [inP] [outP] d1)
  let d5 = d4 { dIn = [inP], dOut = [outP] }
  case diagramIsoEq d3 d5 of
    Left err -> assertFailure (T.unpack err)
    Right ok ->
      if ok then pure () else assertFailure "expected box names to be ignored"

testDuplicateGenTyVars :: Assertion
testDuplicateGenTyVars = do
  let mode = ModeName "M"
  let a = TyVar "a"
  let gen = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdTyVars = [a, a]
        , gdDom = [TVar a]
        , gdCod = [TVar a]
        }
  let doc = Doctrine
        { dName = "DupGenTyVars"
        , dModes = ModeTheory (S.singleton mode) M.empty []
        , dTypes = M.empty
        , dGens = M.fromList [(mode, M.fromList [(gdName gen, gen)])]
        , dCells2 = []
        }
  case validateDoctrine doc of
    Left _ -> pure ()
    Right _ -> assertFailure "expected duplicate gen tyvars to be rejected"

testDuplicateCellTyVars :: Assertion
testDuplicateCellTyVars = do
  let mode = ModeName "M"
  let a = TyVar "a"
  let diag = idD mode [TVar a]
  let cell = Cell2
        { c2Name = "dupCellTyVars"
        , c2Class = Structural
        , c2Orient = Bidirectional
        , c2TyVars = [a, a]
        , c2LHS = diag
        , c2RHS = diag
        }
  let doc = Doctrine
        { dName = "DupCellTyVars"
        , dModes = ModeTheory (S.singleton mode) M.empty []
        , dTypes = M.empty
        , dGens = M.empty
        , dCells2 = [cell]
        }
  case validateDoctrine doc of
    Left _ -> pure ()
    Right _ -> assertFailure "expected duplicate cell tyvars to be rejected"

buildIsoDiagram :: ModeName -> TypeExpr -> Either Text Diagram
buildIsoDiagram mode a = do
  let (p0, d0) = freshPort a (emptyDiagram mode)
  let (p1, d1) = freshPort a d0
  let (p2, d2) = freshPort a d1
  let (p3, d3) = freshPort a d2
  let (p4, d4) = freshPort a d3
  d5 <- addEdgePayload (PGen (GenName "f")) [p0] [p2] d4
  d6 <- addEdgePayload (PGen (GenName "g")) [p1] [p3] d5
  d7 <- addEdgePayload (PGen (GenName "h")) [p2, p3] [p4] d6
  let diag = d7 { dIn = [p0, p1], dOut = [p4] }
  validateDiagram diag
  pure diag

permuteIsoDiagram :: Diagram -> Either Text Diagram
permuteIsoDiagram diag = do
  let ins = dIn diag
  let outs = dOut diag
  case (ins, outs) of
    ([p0, p1], [p4]) -> do
      let p2 = PortId 2
      let p3 = PortId 3
      let e0 = EdgeId 0
      let e1 = EdgeId 1
      let portMap = IM.fromList [ (portKey p2, p3), (portKey p3, p2) ]
      let edgeMap = IM.fromList [ (edgeKey e0, e1), (edgeKey e1, e0) ]
      let remapPort pid =
            case IM.lookup (portKey pid) portMap of
              Just pid' -> pid'
              Nothing -> pid
      let remapEdge eid =
            case IM.lookup (edgeKey eid) edgeMap of
              Just eid' -> eid'
              Nothing -> eid
      let dPortTy' = IM.fromList
            [ (portKey (remapPort (PortId k)), ty)
            | (k, ty) <- IM.toList (dPortTy diag)
            ]
      let dProd' = IM.fromList
            [ (portKey (remapPort (PortId k)), fmap remapEdge prod)
            | (k, prod) <- IM.toList (dProd diag)
            ]
      let dCons' = IM.fromList
            [ (portKey (remapPort (PortId k)), fmap remapEdge cons)
            | (k, cons) <- IM.toList (dCons diag)
            ]
      let remapEdgeRec edge =
            edge
              { eId = remapEdge (eId edge)
              , eIns = map remapPort (eIns edge)
              , eOuts = map remapPort (eOuts edge)
              }
      let dEdges' = IM.fromList
            [ (edgeKey (remapEdge (EdgeId k)), remapEdgeRec edge)
            | (k, edge) <- IM.toList (dEdges diag)
            ]
      let diag' = diag
            { dIn = map remapPort (dIn diag)
            , dOut = map remapPort (dOut diag)
            , dPortTy = dPortTy'
            , dProd = dProd'
            , dCons = dCons'
            , dEdges = dEdges'
            }
      validateDiagram diag'
      pure diag'
    _ -> Left "unexpected boundary shape for permutation"
  where
    portKey (PortId k) = k
    edgeKey (EdgeId k) = k
