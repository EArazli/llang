{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Feedback
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import Strat.Frontend.Env (emptyEnv)
import Strat.Pipeline (defaultFoliationPolicy)
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Poly.Foliation (foliate, SSAStep(..), SSA(..))
import Strat.Poly.Doctrine
import Strat.Poly.Diagram
import Strat.Poly.Graph (EdgePayload(..), ePayload)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.Feedback"
    [ testCase "loop elaborates to explicit feedback payload" testFeedbackElab
    ]


testFeedbackElab :: Assertion
testFeedbackElab = do
  let doc = mkDoctrine
  raw <- require (parseDiagExpr "loop { step }")
  diag <- require (elabDiagExpr emptyEnv doc modeM [] raw)
  assertBool "expected feedback edge in outer graph" (hasFeedback diag)
  ssa <- require (foliate defaultFoliationPolicy doc modeM diag)
  assertBool "expected StepFeedback in SSA" (any isFeedbackStep (ssaSteps ssa))
  where
    isFeedbackStep step =
      case step of
        StepFeedback {} -> True
        _ -> False


hasFeedback :: Diagram -> Bool
hasFeedback diag =
  any isFeedback (IM.elems (dEdges diag))
  where
    isFeedback edge =
      case ePayload edge of
        PFeedback _ -> True
        _ -> False


mkDoctrine :: Doctrine
mkDoctrine =
  Doctrine
    { dName = "D"
    , dModes = mkModes [modeM]
    , dAcyclicModes = S.singleton modeM
    , dAttrSorts = M.empty
    , dTypes = M.fromList [(modeM, M.fromList [(TypeName "T", TypeSig [])])]
    , dGens = M.fromList [(modeM, M.fromList [(GenName "step", genStep)])]
    , dCells2 = []
      , dActions = M.empty
      , dObligations = []
    }


genStep :: GenDecl
genStep =
  GenDecl
    { gdName = GenName "step"
    , gdMode = modeM
    , gdTyVars = []
    , gdTmVars = []
    , gdDom = [InPort tyT]
    , gdCod = [tyT, tyT]
    , gdAttrs = []
    }


modeM :: ModeName
modeM = ModeName "M"


tyT :: TypeExpr
tyT = TCon (TypeRef modeM (TypeName "T")) []


require :: Either Text a -> IO a
require (Left err) = assertFailure (show err) >> fail "unreachable"
require (Right a) = pure a
