{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Foliation
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Pipeline (defaultFoliationPolicy)
import Strat.Poly.Foliation (foliate, forgetSSA, canonicalizeDiagram, SSA(..))
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.Foliation"
    [ testCase "forget(foliate(d)) canonicalizes to d" testForgetFoliate
    , testCase "foliation is deterministic" testDeterminism
    , testCase "port naming keeps unsuffixed boundary/internal names" testUnsuffixedPortNames
    , testCase "SSA boundaries match forgetSSA boundaries" testSsaBoundaryConsistency
    , testCase "identity boundary naming is stable for shared in/out port" testIdentityBoundaryName
    ]


testForgetFoliate :: Assertion
testForgetFoliate = do
  let doc = mkDoctrine
  diag <- require (mkDiag doc)
  ssa <- require (foliate defaultFoliationPolicy doc modeM diag)
  got <- require (canonicalizeDiagram (forgetSSA ssa))
  want <- require (canonicalizeDiagram diag)
  got @?= want


testDeterminism :: Assertion
testDeterminism = do
  let doc = mkDoctrine
  diag <- require (mkDiag doc)
  ssa1 <- require (foliate defaultFoliationPolicy doc modeM diag)
  ssa2 <- require (foliate defaultFoliationPolicy doc modeM diag)
  ssa1 @?= ssa2


testUnsuffixedPortNames :: Assertion
testUnsuffixedPortNames = do
  let doc = mkDoctrine
  diag <- require (mkTwoStepDiag doc)
  ssa <- require (foliate defaultFoliationPolicy doc modeM diag)
  let names = M.elems (ssaPortNames ssa)
  assertBool "expected boundary name p0" ("p0" `elem` names)
  assertBool "expected boundary name p1" ("p1" `elem` names)
  assertBool "expected internal name t0" ("t0" `elem` names)
  assertBool "did not expect suffixed t0_1" ("t0_1" `notElem` names)


testSsaBoundaryConsistency :: Assertion
testSsaBoundaryConsistency = do
  let doc = mkDoctrine
  diag <- require (mkDiag doc)
  ssa <- require (foliate defaultFoliationPolicy doc modeM diag)
  let forgot = forgetSSA ssa
  ssaInputs ssa @?= dIn forgot
  ssaOutputs ssa @?= dOut forgot


testIdentityBoundaryName :: Assertion
testIdentityBoundaryName = do
  let doc = mkDoctrine
      diag = idD modeM [tyT]
  ssa <- require (foliate defaultFoliationPolicy doc modeM diag)
  case dIn (forgetSSA ssa) of
    [p] ->
      case M.lookup p (ssaPortNames ssa) of
        Just name -> name @?= "p0"
        Nothing -> assertFailure "expected boundary port to be named"
    _ -> assertFailure "expected one boundary input port"


mkDiag :: Doctrine -> Either Text Diagram
mkDiag doc = do
  a <- genD modeM [] [tyT] (GenName "a")
  b <- genD modeM [tyT] [tyT] (GenName "b")
  c <- genD modeM [tyT] [] (GenName "c")
  ab <- compD (doctrineTypeTheory doc) b a
  compD (doctrineTypeTheory doc) c ab


mkTwoStepDiag :: Doctrine -> Either Text Diagram
mkTwoStepDiag doc = do
  b1 <- genD modeM [tyT] [tyT] (GenName "b")
  b2 <- genD modeM [tyT] [tyT] (GenName "b")
  compD (doctrineTypeTheory doc) b2 b1


mkDoctrine :: Doctrine
mkDoctrine =
  Doctrine
    { dName = "D"
    , dModes = mkModes [modeM]
    , dAcyclicModes = S.singleton modeM
    , dAttrSorts = M.empty
    , dTypes = M.fromList [(modeM, M.fromList [(TypeName "T", TypeSig [])])]
    , dGens = M.fromList [(modeM, M.fromList [(GenName "a", genA), (GenName "b", genB), (GenName "c", genC)])]
    , dCells2 = []
      , dActions = M.empty
      , dObligations = []
    }


genA :: GenDecl
genA =
  GenDecl
    { gdName = GenName "a"
    , gdMode = modeM
    , gdTyVars = []
    , gdTmVars = []
    , gdDom = []
    , gdCod = [tyT]
    , gdAttrs = []
    }


genB :: GenDecl
genB =
  GenDecl
    { gdName = GenName "b"
    , gdMode = modeM
    , gdTyVars = []
    , gdTmVars = []
    , gdDom = [InPort tyT]
    , gdCod = [tyT]
    , gdAttrs = []
    }


genC :: GenDecl
genC =
  GenDecl
    { gdName = GenName "c"
    , gdMode = modeM
    , gdTyVars = []
    , gdTmVars = []
    , gdDom = [InPort tyT]
    , gdCod = []
    , gdAttrs = []
    }


modeM :: ModeName
modeM = ModeName "M"


tyT :: TypeExpr
tyT = TCon (TypeRef modeM (TypeName "T")) []


require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a
