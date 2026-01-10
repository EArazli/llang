{-# LANGUAGE OverloadedStrings #-}
module Main where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import Data.Text (Text)
import Strat.Meta.Coherence
import Strat.Meta.CriticalPairs
import Strat.Meta.Examples.Monoid
import Strat.Meta.Rewrite
import Strat.Meta.RewriteSystem
import Strat.Meta.Rule
import Strat.Meta.Term.Class
import Strat.Meta.Term.FO
import Strat.Meta.Types

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Strat.Meta"
    [ testCase "match sanity" testMatchSanity
    , testCase "unify sanity" testUnifySanity
    , testCase "applyStep strict mismatch" testApplyStepMismatch
    , testCase "validateJoiner succeeds" testValidateJoiner
    , testCase "monoid critical pairs non-empty" testMonoidCriticalPairs
    , testCase "monoid normalize deterministic" testMonoidNormalize
    ]

ns :: Text -> Ns
ns name = Ns (RuleId name DirLR) 0

v :: Text -> Int -> Term
v name i = TVar (V (ns name) i)

sym :: Text -> Sym
sym = Sym

app :: Text -> [Term] -> Term
app f xs = TApp (sym f) xs

testMatchSanity :: Assertion
testMatchSanity =
  case match pat target of
    Nothing -> assertFailure "expected match"
    Just (Subst subst) -> subst @?= expected
  where
    pat = app "f" [v "p" 0, v "p" 1]
    target = app "f" [app "a" [], v "t" 0]
    expected =
      M.fromList
        [ (V (ns "p") 0, app "a" [])
        , (V (ns "p") 1, v "t" 0)
        ]

testUnifySanity :: Assertion
testUnifySanity = do
  let x = V (ns "u") 0
  let term1 = app "f" [TVar x]
  let term2 = app "f" [app "a" []]
  case unify term1 term2 of
    Nothing -> assertFailure "expected unifier"
    Just (Subst subst) ->
      M.lookup x subst @?= Just (app "a" [])
  let x' = V (ns "occurs") 0
  let occursTerm1 = TVar x'
  let occursTerm2 = app "f" [TVar x']
  unify occursTerm1 occursTerm2 @?= Nothing

testApplyStepMismatch :: Assertion
testApplyStepMismatch =
  applyStep (const rule) step term @?= Nothing
  where
    rid = RuleId "r" DirLR
    x = V (ns "r") 0
    rule =
      Rule
        { ruleId = rid
        , ruleIx = 0
        , ruleName = "r"
        , ruleClass = Computational
        , lhs = app "f" [TVar x]
        , rhs = app "g" [TVar x]
        }
    step = Step rid [] (Subst (M.fromList [(x, app "a" [])]))
    term = app "f" [app "b" []]

testValidateJoiner :: Assertion
testValidateJoiner =
  assertBool "joiner should validate" (validateJoiner (const rule) rs cp joiner)
  where
    rid = RuleId "j" DirLR
    x = V (ns "j") 0
    rule =
      Rule
        { ruleId = rid
        , ruleIx = 0
        , ruleName = "j"
        , ruleClass = Computational
        , lhs = app "f" [TVar x]
        , rhs = TVar x
        }
    rs =
      RewriteSystem
        { rsRules = [rule]
        , rsRuleMap = M.fromList [(rid, rule)]
        }
    a = app "a" []
    term = app "f" [a]
    step = Step rid [] (Subst (M.fromList [(x, a)]))
    cp =
      CriticalPair
        { cpRule1 = rid
        , cpRule2 = rid
        , cpPosIn2 = []
        , cpPeak = term
        , cpLeft = term
        , cpRight = term
        , cpMgu = Subst M.empty
        }
    joiner =
      Joiner
        { joinTerm = a
        , leftDerivation = [step]
        , rightDerivation = [step]
        }

testMonoidCriticalPairs :: Assertion
testMonoidCriticalPairs =
  case monoidCriticalPairs of
    Left err -> assertFailure (show err)
    Right cps -> assertBool "expected non-empty critical pairs" (not (null cps))

testMonoidNormalize :: Assertion
testMonoidNormalize =
  case monoidRewriteSystem of
    Left err -> assertFailure (show err)
    Right rs -> do
      let a = TApp (Sym "a") []
      let term = mTerm (mTerm eTerm a) eTerm
      normalize 10 rs term @?= a
