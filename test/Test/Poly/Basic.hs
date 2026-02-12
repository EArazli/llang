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
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..), TyVar(..), TypeArg(..))
import Strat.Poly.UnifyTy (Subst(..), applySubstTy, normalizeSubst)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Names (BoxName(..))
import Strat.Poly.Diagram
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..), InputShape(..), validateDoctrine)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Common.Rules (RuleClass(..), Orientation(..))
import Strat.Poly.TypeTheory (modeOnlyTypeTheory)
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
  , unPortId
  , unEdgeId
  )
import Test.Poly.Helpers (mkModes)


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
    , testCase "unionDisjointIntMap rejects collisions" testUnionDisjoint
    , testCase "applySubstTy chases substitutions" testApplySubstChase
    , testCase "applySubstTy handles cycles" testApplySubstCycle
    , testCase "normalizeSubst drops identity" testNormalizeSubstIdentity
    , testCase "diagram iso ignores box names" testDiagramIsoBoxName
    , testCase "validateDoctrine rejects duplicate gen tyvars" testDuplicateGenTyVars
    , testCase "validateDoctrine rejects duplicate cell tyvars" testDuplicateCellTyVars
    , testCase "validateDoctrine rejects RHS fresh tyvars" testRejectRHSTyVars
    , testCase "validateDoctrine accepts RHS vars from LHS" testAcceptRHSTyVars
    , testCase "validateDoctrine rejects empty LHS rule" testRejectEmptyLHS
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

tvar :: ModeName -> Text -> TyVar
tvar mode name = TyVar { tvName = name, tvMode = mode }

tcon :: ModeName -> Text -> [TypeExpr] -> TypeExpr
tcon mode name args = TCon (TypeRef mode (TypeName name)) (map TAType args)


testDiagramDomCod :: Assertion
testDiagramDomCod = do
  let mode = ModeName "Cart"
  let a = tcon mode "A" []
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
  let a = tcon mode "A" []
  let b = tcon mode "B" []
  let g = idD mode [a]
  let f = idD mode [b]
  case compDTT (modeOnlyTypeTheory (mkModes [mode])) g f of
    Left _ -> pure ()
    Right _ -> assertFailure "expected boundary mismatch"


testTensorModeMismatch :: Assertion
testTensorModeMismatch = do
  let modeA = ModeName "A"
  let modeB = ModeName "B"
  let aA = tcon modeA "A" []
  let aB = tcon modeB "A" []
  let d1 = idD modeA [aA]
  let d2 = idD modeB [aB]
  case tensorD d1 d2 of
    Left _ -> pure ()
    Right _ -> assertFailure "expected mode mismatch"

testValidateStaleIncidence :: Assertion
testValidateStaleIncidence = do
  let mode = ModeName "Cart"
  let a = tcon mode "A" []
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
  let a = tcon mode "A" []
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
  let a = tcon mode "A" []
  let diag = idD mode [a]
  let bad = diag { dOut = [] }
  case validateDiagram bad of
    Left _ -> pure ()
    Right _ -> assertFailure "expected validation failure for unused input"

testValidateDuplicateOutputs :: Assertion
testValidateDuplicateOutputs = do
  let mode = ModeName "Cart"
  let a = tcon mode "A" []
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
  let a = tcon mode "A" []
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

testUnionDisjoint :: Assertion
testUnionDisjoint = do
  let left = IM.fromList [(0 :: Int, "a")]
  let right = IM.fromList [(0 :: Int, "b")]
  case unionDisjointIntMap "test" left right of
    Left _ -> pure ()
    Right _ -> assertFailure "expected union collision error"

testApplySubstChase :: Assertion
testApplySubstChase = do
  let mode = ModeName "M"
  let a = tvar mode "a"
  let b = tvar mode "b"
  let c = tcon mode "C" []
  let tt = modeOnlyTypeTheory (mkModes [mode])
  let subst = Subst (M.fromList [(a, TVar b), (b, c)]) M.empty
  ty <- require (applySubstTy tt subst (TVar a))
  ty @?= c

testApplySubstCycle :: Assertion
testApplySubstCycle = do
  let mode = ModeName "M"
  let a = tvar mode "a"
  let b = tvar mode "b"
  let tt = modeOnlyTypeTheory (mkModes [mode])
  let subst = Subst (M.fromList [(a, TVar b), (b, TVar a)]) M.empty
  ty <- require (applySubstTy tt subst (TVar a))
  ty @?= TVar a

testNormalizeSubstIdentity :: Assertion
testNormalizeSubstIdentity = do
  let mode = ModeName "M"
  let a = tvar mode "a"
  let tt = modeOnlyTypeTheory (mkModes [mode])
  subst <- require (normalizeSubst tt (Subst (M.fromList [(a, TVar a)]) M.empty))
  sTy subst @?= M.empty

testDiagramIsoBoxName :: Assertion
testDiagramIsoBoxName = do
  let mode = ModeName "M"
  let a = tcon mode "A" []
  let inner = idD mode [a]
  let (inP, d0) = freshPort a (emptyDiagram mode [])
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
  let a = tvar mode "a"
  let gen = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdTyVars = [a, a]
        , gdIxVars = []
    , gdDom = map InPort [TVar a]
        , gdCod = [TVar a]
        , gdAttrs = []
        }
  let doc = Doctrine
        { dName = "DupGenTyVars"
        , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
        , dTypes = M.empty
        , dGens = M.fromList [(mode, M.fromList [(gdName gen, gen)])]
        , dCells2 = []
        , dAttrSorts = M.empty
        }
  case validateDoctrine doc of
    Left _ -> pure ()
    Right _ -> assertFailure "expected duplicate gen tyvars to be rejected"

testDuplicateCellTyVars :: Assertion
testDuplicateCellTyVars = do
  let mode = ModeName "M"
  let a = tvar mode "a"
  let diag = idD mode [TVar a]
  let cell = Cell2
        { c2Name = "dupCellTyVars"
        , c2Class = Structural
        , c2Orient = Bidirectional
        , c2TyVars = [a, a]
        , c2IxVars = []
        , c2LHS = diag
        , c2RHS = diag
        }
  let doc = Doctrine
        { dName = "DupCellTyVars"
        , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
        , dTypes = M.empty
        , dGens = M.empty
        , dCells2 = [cell]
        , dAttrSorts = M.empty
        }
  case validateDoctrine doc of
    Left _ -> pure ()
    Right _ -> assertFailure "expected duplicate cell tyvars to be rejected"

testRejectRHSTyVars :: Assertion
testRejectRHSTyVars = do
  let mode = ModeName "M"
  let aName = TypeName "A"
  let bVar = tvar mode "b"
  let gen = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdTyVars = []
        , gdIxVars = []
    , gdDom = map InPort [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        , gdAttrs = []
        }
  lhs <- require (genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName gen))
  rhs <- require (genD mode [TVar bVar] [TVar bVar] (gdName gen))
  let cell = Cell2
        { c2Name = "rhs_fresh"
        , c2Class = Computational
        , c2Orient = LR
        , c2TyVars = []
        , c2IxVars = []
        , c2LHS = lhs
        , c2RHS = rhs
        }
  let doc = Doctrine
        { dName = "D"
        , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
        , dTypes = M.fromList [(mode, M.fromList [(aName, TypeSig [])])]
        , dGens = M.fromList [(mode, M.fromList [(gdName gen, gen)])]
        , dCells2 = [cell]
        , dAttrSorts = M.empty
        }
  case validateDoctrine doc of
    Left _ -> pure ()
    Right _ -> assertFailure "expected RHS fresh tyvars to be rejected"

testAcceptRHSTyVars :: Assertion
testAcceptRHSTyVars = do
  let mode = ModeName "M"
  let aName = TypeName "A"
  let aVar = tvar mode "a"
  let gen = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdTyVars = [aVar]
        , gdIxVars = []
    , gdDom = map InPort [TVar aVar]
        , gdCod = [TVar aVar]
        , gdAttrs = []
        }
  lhs <- require (genD mode [TVar aVar] [TVar aVar] (gdName gen))
  rhs <- require (genD mode [TVar aVar] [TVar aVar] (gdName gen))
  let cell = Cell2
        { c2Name = "rhs_ok"
        , c2Class = Computational
        , c2Orient = LR
        , c2TyVars = [aVar]
        , c2IxVars = []
        , c2LHS = lhs
        , c2RHS = rhs
        }
  let doc = Doctrine
        { dName = "D"
        , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
        , dTypes = M.fromList [(mode, M.fromList [(aName, TypeSig [])])]
        , dGens = M.fromList [(mode, M.fromList [(gdName gen, gen)])]
        , dCells2 = [cell]
        , dAttrSorts = M.empty
        }
  case validateDoctrine doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()

testRejectEmptyLHS :: Assertion
testRejectEmptyLHS = do
  let mode = ModeName "M"
  let aName = TypeName "A"
  let lhs = idD mode [tcon mode "A" []]
  let rhs = idD mode [tcon mode "A" []]
  let cell = Cell2
        { c2Name = "empty_lhs"
        , c2Class = Computational
        , c2Orient = LR
        , c2TyVars = []
        , c2IxVars = []
        , c2LHS = lhs
        , c2RHS = rhs
        }
  let doc = Doctrine
        { dName = "D"
        , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
        , dTypes = M.fromList [(mode, M.fromList [(aName, TypeSig [])])]
        , dGens = M.empty
        , dCells2 = [cell]
        , dAttrSorts = M.empty
        }
  case validateDoctrine doc of
    Left _ -> pure ()
    Right _ -> assertFailure "expected empty LHS rule to be rejected"

buildIsoDiagram :: ModeName -> TypeExpr -> Either Text Diagram
buildIsoDiagram mode a = do
  let (p0, d0) = freshPort a (emptyDiagram mode [])
  let (p1, d1) = freshPort a d0
  let (p2, d2) = freshPort a d1
  let (p3, d3) = freshPort a d2
  let (p4, d4) = freshPort a d3
  d5 <- addEdgePayload (PGen (GenName "f") M.empty []) [p0] [p2] d4
  d6 <- addEdgePayload (PGen (GenName "g") M.empty []) [p1] [p3] d5
  d7 <- addEdgePayload (PGen (GenName "h") M.empty []) [p2, p3] [p4] d6
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
      let portMap = IM.fromList [(unPortId p2, p3), (unPortId p3, p2)]
      let edgeMap = IM.fromList [(unEdgeId e0, e1), (unEdgeId e1, e0)]
      let remapPort pid =
            case IM.lookup (unPortId pid) portMap of
              Just pid' -> pid'
              Nothing -> pid
      let remapEdge eid =
            case IM.lookup (unEdgeId eid) edgeMap of
              Just eid' -> eid'
              Nothing -> eid
      let dPortTy' = IM.fromList
            [ (unPortId (remapPort (PortId k)), ty)
            | (k, ty) <- IM.toList (dPortTy diag)
            ]
      let dPortLabel' = IM.fromList
            [ (unPortId (remapPort (PortId k)), label)
            | (k, label) <- IM.toList (dPortLabel diag)
            ]
      let dProd' = IM.fromList
            [ (unPortId (remapPort (PortId k)), fmap remapEdge prod)
            | (k, prod) <- IM.toList (dProd diag)
            ]
      let dCons' = IM.fromList
            [ (unPortId (remapPort (PortId k)), fmap remapEdge cons)
            | (k, cons) <- IM.toList (dCons diag)
            ]
      let remapEdgeRec edge =
            edge
              { eId = remapEdge (eId edge)
              , eIns = map remapPort (eIns edge)
              , eOuts = map remapPort (eOuts edge)
              }
      let dEdges' = IM.fromList
            [ (unEdgeId (remapEdge (EdgeId k)), remapEdgeRec edge)
            | (k, edge) <- IM.toList (dEdges diag)
            ]
      let diag' = diag
            { dIn = map remapPort (dIn diag)
            , dOut = map remapPort (dOut diag)
            , dPortTy = dPortTy'
            , dPortLabel = dPortLabel'
            , dProd = dProd'
            , dCons = dCons'
            , dEdges = dEdges'
            }
      validateDiagram diag'
      pure diag'
    _ -> Left "unexpected boundary shape for permutation"
