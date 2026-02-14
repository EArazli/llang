{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.CriticalPairs
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Common.Rules (RuleClass(..))
import Strat.Poly.ModeTheory
import Strat.Poly.TypeExpr
import Strat.Poly.Names
import Strat.Poly.Diagram
import Strat.Poly.Rewrite (RewriteRule(..))
import Strat.Poly.CriticalPairs
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Doctrine (Doctrine(..), validateDoctrine)
import Strat.Common.Rules (RewritePolicy(..), Orientation(..))
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.CriticalPairs"
    [ testCase "critical pairs respect mode equations in overlap matching" testCriticalPairsRespectModeEq
    , testCase "critical pairs freshen colliding type variable names across rules" testCriticalPairsFreshenTyVars
    , testCase "critical pairs fail when dependent substitution fails" testCriticalPairsFailOnSubstFailure
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

testCriticalPairsRespectModeEq :: Assertion
testCriticalPairsRespectModeEq = do
  let mode = ModeName "M"
  let modF = ModName "F"
  let modU = ModName "U"
  let fExpr = ModExpr { meSrc = mode, meTgt = mode, mePath = [modF] }
  let uExpr = ModExpr { meSrc = mode, meTgt = mode, mePath = [modU] }
  let baseTy = TCon (TypeRef mode (TypeName "Base")) []
  let ufBaseTy = TMod uExpr (TMod fExpr baseTy)
  let mt =
        ModeTheory
          { mtModes = M.singleton mode (ModeInfo mode)
          , mtDecls =
              M.fromList
                [ (modF, ModDecl modF mode mode)
                , (modU, ModDecl modU mode mode)
                ]
          , mtEqns =
              [ ModEqn
                  (ModExpr { meSrc = mode, meTgt = mode, mePath = [modF, modU] })
                  (ModExpr { meSrc = mode, meTgt = mode, mePath = [] })
              ]
          }
  lhsUF <- require (genD mode [ufBaseTy] [ufBaseTy] (GenName "g"))
  lhsBase <- require (genD mode [baseTy] [baseTy] (GenName "g"))
  let ruleUF =
        RewriteRule
          { rrName = "rule.uf"
          , rrLHS = lhsUF
          , rrRHS = lhsUF
          , rrTyVars = []
          , rrTmVars = []
          }
  let ruleBase =
        RewriteRule
          { rrName = "rule.base"
          , rrLHS = lhsBase
          , rrRHS = lhsBase
          , rrTyVars = []
          , rrTmVars = []
          }
  let infoUF = RuleInfo { riLabel = "rule.uf", riRule = ruleUF, riClass = Structural }
  let infoBase = RuleInfo { riLabel = "rule.base", riRule = ruleBase, riClass = Computational }
  pairs <- require (criticalPairsForRules mt CP_StructuralVsComputational [infoUF, infoBase])
  assertBool "expected cross-rule overlap under U.F -> id mode equation" (not (null pairs))

testCriticalPairsFreshenTyVars :: Assertion
testCriticalPairsFreshenTyVars = do
  let mode = ModeName "M"
  let a = TyVar { tvName = "a", tvMode = mode }
  let baseTy = TCon (TypeRef mode (TypeName "B")) []
  g1 <- require (genD mode [baseTy] [baseTy] (GenName "g"))
  h1 <- require (genD mode [TVar a] [TVar a] (GenName "h1"))
  lhs1 <- require (tensorD g1 h1)
  g2 <- require (genD mode [baseTy] [baseTy] (GenName "g"))
  h2 <- require (genD mode [TVar a] [TVar a] (GenName "h2"))
  lhs2 <- require (tensorD g2 h2)
  let rule1 =
        RewriteRule
          { rrName = "rule.ty1"
          , rrLHS = lhs1
          , rrRHS = lhs1
          , rrTyVars = [a]
          , rrTmVars = []
          }
  let rule2 =
        RewriteRule
          { rrName = "rule.ty2"
          , rrLHS = lhs2
          , rrRHS = lhs2
          , rrTyVars = [a]
          , rrTmVars = []
          }
  let info1 = RuleInfo { riLabel = "rule.ty1", riRule = rule1, riClass = Structural }
  let info2 = RuleInfo { riLabel = "rule.ty2", riRule = rule2, riClass = Structural }
  pairs <- require (criticalPairsForRules (mkModes [mode]) CP_All [info1, info2])
  let cross =
        [ cpOverlap (cpiPair info)
        | info <- pairs
        , let aName = cpRule1 (cpiPair info)
        , let bName = cpRule2 (cpiPair info)
        , (aName == "rule.ty1" && bName == "rule.ty2") || (aName == "rule.ty2" && bName == "rule.ty1")
        ]
  assertBool "expected cross-rule critical pair" (not (null cross))
  assertBool "expected overlap to keep distinct tyvars from both rules" (any (\d -> S.size (freeTyVarsDiagram d) >= 2) cross)

testCriticalPairsFailOnSubstFailure :: Assertion
testCriticalPairsFailOnSubstFailure = do
  let mode = ModeName "M"
  let aTy = TCon (TypeRef mode (TypeName "A")) []
  let badTmSort = TCon (TypeRef mode (TypeName "BadSort")) [TAType aTy]
  lhs <- require (genDTm mode [badTmSort] [aTy] [aTy] (GenName "g"))
  let cell =
        Cell2
          { c2Name = "bad-subst"
          , c2Class = Structural
          , c2Orient = LR
          , c2TyVars = []
          , c2TmVars = []
          , c2LHS = lhs
          , c2RHS = lhs
          }
  let doc =
        Doctrine
          { dName = "D"
          , dModes = mkModes [mode]
          , dAcyclicModes = S.empty
          , dAttrSorts = M.empty
          , dTypes = M.empty
          , dGens = M.empty
          , dCells2 = [cell]
          , dActions = M.empty
          , dObligations = []
          }
  _ <- require (validateDoctrine doc)
  case criticalPairsForDoctrine CP_All UseAllOriented doc of
    Left err -> assertBool "expected substitution-failure error" ("substitution failure" `T.isInfixOf` err)
    Right _ -> assertFailure "expected critical pair generation to fail"
