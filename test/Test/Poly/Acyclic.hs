{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Acyclic
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import Strat.Pipeline (FragmentDecl(..))
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Graph (EdgePayload(..), addEdgePayload, emptyDiagram, freshPort)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
import Strat.Poly.Quote (quoteProgram)
import Test.Poly.Helpers (mkModes, withSelfClassifiedCtors)


tests :: TestTree
tests =
  testGroup
    "Poly.Acyclic"
    [ testCase "cycles in acyclic mode are rejected" testRejectCycle
    ]


testRejectCycle :: Assertion
testRejectCycle = do
  let doc = mkDoctrine
  let (p0, d0) = freshPort tyT (emptyDiagram modeM [])
  let (p1, d1) = freshPort tyT d0
  d2 <- require (addEdgePayload (PGen (GenName "f") [] []) [p0] [p1] d1)
  d3 <- require (addEdgePayload (PGen (GenName "g") [] []) [p1] [p0] d2)
  let cyc = d3 { dIn = [], dOut = [] }
  case quoteProgram doc modeM fragmentResidual cyc of
    Left err ->
      assertBool ("expected acyclic-cycle error, got: " <> T.unpack err) ("cyclic" `T.isInfixOf` T.toLower err)
    Right _ ->
      assertFailure "expected quoteProgram to reject cycle"


mkDoctrine :: Doctrine
mkDoctrine =
  withSelfClassifiedCtors
    [(modeM, [(ObjName "T", [])])]
    Doctrine
      { dName = "D"
      , dModes = mkModes [modeM]
      , dAcyclicModes = S.singleton modeM
            , dGens = M.empty
      , dCells2 = []
      , dBuiltins = []
      , dActions = M.empty
      , dObligations = []
      }


modeM :: ModeName
modeM = ModeName "M"


tyT :: Obj
tyT = mkCon (ObjRef modeM (ObjName "T")) []


fragmentResidual :: FragmentDecl
fragmentResidual =
  FragmentDecl
    { frName = "Frag"
    , frBase = "D"
    , frMode = "M"
    , frIncludedGens = S.empty
    , frCrossBinders = False
    , frCrossBoxes = False
    , frCrossFeedback = False
    }


require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a
