{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.CriticalPairs
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Strat.Common.Rules (RuleClass(..))
import Strat.Poly.ModeTheory
import Strat.Poly.TypeExpr
import Strat.Poly.Names
import Strat.Poly.Diagram
import Strat.Poly.Rewrite (RewriteRule(..))
import Strat.Poly.CriticalPairs


tests :: TestTree
tests =
  testGroup
    "Poly.CriticalPairs"
    [ testCase "critical pairs respect mode equations in overlap matching" testCriticalPairsRespectModeEq
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
          { mtModes = M.singleton mode (ModeInfo mode Linear)
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
          , mtAdjs = []
          }
  lhsUF <- require (genD mode [ufBaseTy] [ufBaseTy] (GenName "g"))
  lhsBase <- require (genD mode [baseTy] [baseTy] (GenName "g"))
  let ruleUF =
        RewriteRule
          { rrName = "rule.uf"
          , rrLHS = lhsUF
          , rrRHS = lhsUF
          , rrTyVars = []
          }
  let ruleBase =
        RewriteRule
          { rrName = "rule.base"
          , rrLHS = lhsBase
          , rrRHS = lhsBase
          , rrTyVars = []
          }
  let infoUF = RuleInfo { riLabel = "rule.uf", riRule = ruleUF, riClass = Structural }
  let infoBase = RuleInfo { riLabel = "rule.base", riRule = ruleBase, riClass = Computational }
  pairs <- require (criticalPairsForRules mt CP_StructuralVsComputational [infoUF, infoBase])
  assertBool "expected cross-rule overlap under U.F -> id mode equation" (not (null pairs))
