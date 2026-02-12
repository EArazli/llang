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
import Strat.Poly.Foliation (foliate, forgetSSA, canonicalizeDiagram)
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


mkDiag :: Doctrine -> Either Text Diagram
mkDiag doc = do
  a <- genD modeM [] [tyT] (GenName "a")
  b <- genD modeM [tyT] [tyT] (GenName "b")
  c <- genD modeM [tyT] [] (GenName "c")
  ab <- compDTT (doctrineTypeTheory doc) b a
  compDTT (doctrineTypeTheory doc) c ab


mkDoctrine :: Doctrine
mkDoctrine =
  Doctrine
    { dName = "D"
    , dModes = mkModes [modeM]
    , dAcyclicModes = S.singleton modeM
    , dIndexModes = S.empty
    , dIxTheory = M.empty
    , dAttrSorts = M.empty
    , dTypes = M.fromList [(modeM, M.fromList [(TypeName "T", TypeSig [])])]
    , dGens = M.fromList [(modeM, M.fromList [(GenName "a", genA), (GenName "b", genB), (GenName "c", genC)])]
    , dCells2 = []
    }


genA :: GenDecl
genA =
  GenDecl
    { gdName = GenName "a"
    , gdMode = modeM
    , gdTyVars = []
    , gdIxVars = []
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
    , gdIxVars = []
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
    , gdIxVars = []
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
