{-# LANGUAGE OverloadedStrings #-}
module Main where

import Test.Tasty
import Test.Tasty.HUnit
import Data.List (find)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import Strat.Meta.Coherence
import Strat.Meta.CriticalPairs
import Strat.Meta.Examples.Monoid
import Strat.Meta.Presentation
import Strat.Meta.Rewrite
import Strat.Meta.RewriteSystem hiding (mkRule)
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
    , testCase "match repeated var" testMatchRepeatedVar
    , testCase "unify sanity" testUnifySanity
    , testCase "unify applies substitution" testUnifyAppliesSubst
    , testCase "applySubst recursive" testApplySubstRecursive
    , testCase "applyStep strict mismatch" testApplyStepMismatch
    , testCase "validateJoiner succeeds" testValidateJoiner
    , testCase "validateJoiner fails on wrong join" testValidateJoinerWrongJoin
    , testCase "validateJoiner fails on wrong rule" testValidateJoinerWrongRule
    , testCase "compile RL orientation" testCompileRLOrientation
    , testCase "compile bidirectional" testCompileBidirectional
    , testCase "compile unoriented skipped" testCompileUnorientedSkipped
    , testCase "compile structural as bidirectional" testCompileStructuralAsBidirectional
    , testCase "compile duplicate equation names rejected" testCompileDuplicateEqNames
    , testCase "compile UseOnlyComputationalLR skips RL" testCompileUseOnlyComputationalLRSkipsRL
    , testCase "monoid critical pairs non-empty" testMonoidCriticalPairs
    , testCase "monoid critical pair non-trivial" testMonoidCriticalPairsNonTrivial
    , testCase "monoid normalize deterministic" testMonoidNormalize
    , testCase "critical pairs include root overlaps" testCriticalPairsRootOverlap
    , testCase "critical pairs exclude variable overlap" testCriticalPairsExcludeVarOverlap
    , testCase "critical pairs exclude inner variable overlap" testCriticalPairsExcludeInnerVarOverlap
    , testCase "critical pairs freshen self-overlap" testCriticalPairsSelfOverlapFreshening
    , testCase "critical pairs CPMode filtering" testCriticalPairsCPModeFiltering
    , testCase "critical pair soundness" testCriticalPairSoundness
    , testCase "rewriteOnce orders positions" testRewriteOncePositionOrder
    , testCase "rewriteOnce orders deeper positions" testRewriteOncePositionOrderDeep
    , testCase "rewriteOnce orders rules" testRewriteOnceRuleOrder
    , testCase "rewriteOnce rule order same position" testRewriteOnceRuleOrderSamePos
    , testCase "normalize chooses first rule" testNormalizeChoosesFirstRule
    , testCase "normalize fuel edge cases" testNormalizeFuelEdgeCases
    ]

ns :: Text -> Ns
ns name = Ns (RuleId name DirLR) 0

v :: Text -> Int -> Term
v name i = TVar (V (ns name) i)

sym :: Text -> Sym
sym = Sym

app :: Text -> [Term] -> Term
app f xs = TApp (sym f) xs

constTerm :: Text -> Term
constTerm name = app name []

mkRuleWith :: RuleClass -> Text -> Int -> Term -> Term -> Rule Term
mkRuleWith cls name ix l r =
  Rule
    { ruleId = RuleId name DirLR
    , ruleIx = ix
    , ruleName = name
    , ruleClass = cls
    , lhs = l
    , rhs = r
    }

mkRule :: Text -> Int -> Term -> Term -> Rule Term
mkRule = mkRuleWith Computational

mkRS :: [Rule Term] -> RewriteSystem Term
mkRS rules =
  RewriteSystem
    { rsRules = rules
    , rsRuleMap = M.fromList [(ruleId r, r) | r <- rules]
    }

mkEq :: Text -> RuleClass -> Orientation -> Term -> Term -> Equation Term
mkEq name cls orient l r =
  Equation
    { eqName = name
    , eqClass = cls
    , eqOrient = orient
    , eqLHS = l
    , eqRHS = r
    }

renameRuleNs :: Ns -> Rule Term -> Rule Term
renameRuleNs ns' r =
  r
    { lhs = renameVars (setNs ns') (lhs r)
    , rhs = renameVars (setNs ns') (rhs r)
    }

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

testMatchRepeatedVar :: Assertion
testMatchRepeatedVar = do
  match pat badTarget @?= Nothing
  case match pat goodTarget of
    Nothing -> assertFailure "expected repeated-var match"
    Just (Subst subst) -> do
      M.size subst @?= 1
      M.lookup (V (ns "p") 0) subst @?= Just (constTerm "a")
  where
    x = v "p" 0
    pat = app "f" [x, x]
    badTarget = app "f" [constTerm "a", constTerm "b"]
    goodTarget = app "f" [constTerm "a", constTerm "a"]

testUnifySanity :: Assertion
testUnifySanity = do
  let x = V (ns "u") 0
  let term1 = app "f" [TVar x]
  let term2 = app "f" [constTerm "a"]
  case unify term1 term2 of
    Nothing -> assertFailure "expected unifier"
    Just (Subst subst) ->
      M.lookup x subst @?= Just (constTerm "a")
  let x' = V (ns "occurs") 0
  let occursTerm1 = TVar x'
  let occursTerm2 = app "f" [TVar x']
  unify occursTerm1 occursTerm2 @?= Nothing

testUnifyAppliesSubst :: Assertion
testUnifyAppliesSubst = do
  case unify t1 t2 of
    Nothing -> assertFailure "expected unifier"
    Just subst -> do
      applySubst subst t1 @?= applySubst subst t2
      applySubst subst (TVar x) @?= constTerm "a"
      applySubst subst (TVar y) @?= constTerm "a"
  where
    x = V (ns "u2") 0
    y = V (ns "u2") 1
    t1 = app "f" [TVar x, TVar y]
    t2 = app "f" [TVar y, constTerm "a"]

testApplySubstRecursive :: Assertion
testApplySubstRecursive = do
  let x = V (ns "s") 0
  let y = V (ns "s") 1
  let s1 = Subst (M.fromList [(x, TVar y), (y, constTerm "a")])
  applySubst s1 (TVar x) @?= constTerm "a"
  let s2 = Subst (M.fromList [(x, app "g" [TVar y]), (y, constTerm "a")])
  applySubst s2 (app "f" [TVar x]) @?= app "f" [app "g" [constTerm "a"]]

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
  assertBool "joiner should validate" (validateJoiner (getRule rs) rs cp joiner)
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

testValidateJoinerWrongJoin :: Assertion
testValidateJoinerWrongJoin =
  assertBool "joiner should fail on wrong join term" (not (validateJoiner (getRule rs) rs cp badJoiner))
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
    rs = mkRS [rule]
    a = constTerm "a"
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
    badJoiner =
      Joiner
        { joinTerm = constTerm "b"
        , leftDerivation = [step]
        , rightDerivation = [step]
        }

testValidateJoinerWrongRule :: Assertion
testValidateJoinerWrongRule =
  assertBool "joiner should fail on wrong rule" (not (validateJoiner (getRule rs) rs cp badJoiner))
  where
    ridGood = RuleId "j-good" DirLR
    ridBad = RuleId "j-bad" DirLR
    xGood = V (Ns ridGood 0) 0
    xBad = V (Ns ridBad 0) 0
    ruleGood =
      Rule
        { ruleId = ridGood
        , ruleIx = 0
        , ruleName = "j-good"
        , ruleClass = Computational
        , lhs = app "f" [TVar xGood]
        , rhs = TVar xGood
        }
    ruleBad =
      Rule
        { ruleId = ridBad
        , ruleIx = 1
        , ruleName = "j-bad"
        , ruleClass = Computational
        , lhs = app "f" [TVar xBad]
        , rhs = app "g" [TVar xBad]
        }
    rs = mkRS [ruleGood, ruleBad]
    a = constTerm "a"
    term = app "f" [a]
    badStep = Step ridBad [] (Subst (M.fromList [(xBad, a)]))
    cp =
      CriticalPair
        { cpRule1 = ridGood
        , cpRule2 = ridGood
        , cpPosIn2 = []
        , cpPeak = term
        , cpLeft = term
        , cpRight = term
        , cpMgu = Subst M.empty
        }
    badJoiner =
      Joiner
        { joinTerm = a
        , leftDerivation = [badStep]
        , rightDerivation = [badStep]
        }

testCompileRLOrientation :: Assertion
testCompileRLOrientation =
  case compileRewriteSystem UseAllOriented pres of
    Left err -> assertFailure (show err)
    Right rs ->
      case rsRules rs of
        [r] -> do
          ruleId r @?= RuleId "rl-eq" DirRL
          lhs r @?= constTerm "b"
          rhs r @?= constTerm "a"
        _ -> assertFailure "expected exactly one rule"
  where
    pres =
      Presentation
        { presName = "rl"
        , presEqs =
            [ mkEq "rl-eq" Computational RL (constTerm "a") (constTerm "b")
            ]
        }

testCompileBidirectional :: Assertion
testCompileBidirectional =
  case compileRewriteSystem UseAllOriented pres of
    Left err -> assertFailure (show err)
    Right rs -> do
      map ruleId (rsRules rs) @?= [RuleId "bi" DirLR, RuleId "bi" DirRL]
      map ruleIx (rsRules rs) @?= [0, 1]
  where
    pres =
      Presentation
        { presName = "bi"
        , presEqs =
            [ mkEq "bi" Computational Bidirectional (constTerm "a") (constTerm "b")
            ]
        }

testCompileUnorientedSkipped :: Assertion
testCompileUnorientedSkipped = do
  case compileRewriteSystem UseOnlyComputationalLR pres of
    Left err -> assertFailure (show err)
    Right rs -> rsRules rs @?= []
  case compileRewriteSystem UseAllOriented pres of
    Left err -> assertFailure (show err)
    Right rs -> rsRules rs @?= []
  where
    pres =
      Presentation
        { presName = "uo"
        , presEqs =
            [ mkEq "uo" Computational Unoriented (constTerm "a") (constTerm "b")
            ]
        }

testCompileStructuralAsBidirectional :: Assertion
testCompileStructuralAsBidirectional =
  case compileRewriteSystem UseStructuralAsBidirectional pres of
    Left err -> assertFailure (show err)
    Right rs -> do
      map ruleId (rsRules rs)
        @?= [ RuleId "struct" DirLR
            , RuleId "struct" DirRL
            , RuleId "comp" DirRL
            ]
  where
    pres =
      Presentation
        { presName = "struct"
        , presEqs =
            [ mkEq "struct" Structural Unoriented (constTerm "a") (constTerm "b")
            , mkEq "comp" Computational RL (constTerm "c") (constTerm "d")
            ]
        }

testCompileDuplicateEqNames :: Assertion
testCompileDuplicateEqNames =
  case compileRewriteSystem UseAllOriented pres of
    Left _ -> pure ()
    Right _ -> assertFailure "expected duplicate equation name rejection"
  where
    pres =
      Presentation
        { presName = "dups"
        , presEqs =
            [ mkEq "dup" Computational LR (constTerm "a") (constTerm "b")
            , mkEq "dup" Computational RL (constTerm "c") (constTerm "d")
            ]
        }

testCompileUseOnlyComputationalLRSkipsRL :: Assertion
testCompileUseOnlyComputationalLRSkipsRL =
  case compileRewriteSystem UseOnlyComputationalLR pres of
    Left err -> assertFailure (show err)
    Right rs -> rsRules rs @?= []
  where
    pres =
      Presentation
        { presName = "skip-rl"
        , presEqs =
            [ mkEq "rl-eq" Computational RL (constTerm "a") (constTerm "b")
            ]
        }

testMonoidCriticalPairs :: Assertion
testMonoidCriticalPairs =
  case monoidCriticalPairs of
    Left err -> assertFailure (show err)
    Right cps -> assertBool "expected non-empty critical pairs" (not (null cps))

testMonoidCriticalPairsNonTrivial :: Assertion
testMonoidCriticalPairsNonTrivial =
  case monoidCriticalPairs of
    Left err -> assertFailure (show err)
    Right cps ->
      assertBool "expected a non-trivial critical pair" (any (\cp -> cpLeft cp /= cpRight cp) cps)

testMonoidNormalize :: Assertion
testMonoidNormalize =
  case monoidRewriteSystem of
    Left err -> assertFailure (show err)
    Right rs -> do
      let a = constTerm "a"
      let term = mTerm (mTerm eTerm a) eTerm
      normalize 10 rs term @?= a

testCriticalPairsRootOverlap :: Assertion
testCriticalPairsRootOverlap = do
  let rid1 = RuleId "r1" DirLR
  let rid2 = RuleId "r2" DirLR
  let x = V (Ns rid1 0) 0
  let y = V (Ns rid2 0) 0
  let r1 = mkRule "r1" 0 (app "f" [TVar x]) (app "g" [TVar x])
  let r2 = mkRule "r2" 1 (app "f" [TVar y]) (app "h" [TVar y])
  let rs = mkRS [r1, r2]
  let cps = criticalPairs CP_All (getRule rs) rs
  assertBool "expected root overlap critical pair"
    (any (\cp -> cpRule1 cp == rid1 && cpRule2 cp == rid2 && cpPosIn2 cp == [] && cpLeft cp /= cpRight cp) cps)

testCriticalPairsExcludeVarOverlap :: Assertion
testCriticalPairsExcludeVarOverlap = do
  let rid1 = RuleId "r1" DirLR
  let ridVar = RuleId "var" DirLR
  let x = V (Ns rid1 0) 0
  let vvar = V (Ns ridVar 0) 0
  let r1 = mkRule "r1" 0 (app "f" [TVar x]) (app "g" [TVar x])
  let rVar = mkRule "var" 1 (TVar vvar) (app "h" [TVar vvar])
  let rs = mkRS [r1, rVar]
  let cps = criticalPairs CP_All (getRule rs) rs
  assertBool "expected no overlaps into variable lhs"
    (all (\cp -> cpRule2 cp /= ridVar) cps)

testCriticalPairsExcludeInnerVarOverlap :: Assertion
testCriticalPairsExcludeInnerVarOverlap = do
  let rid2 = RuleId "r2" DirLR
  let x = V (Ns rid2 0) 0
  let r1 = mkRule "r1" 0 (constTerm "a") (constTerm "b")
  let r2 = mkRule "r2" 1 (app "f" [TVar x]) (app "g" [TVar x])
  let rs = mkRS [r1, r2]
  let cps = criticalPairs CP_All (getRule rs) rs
  assertBool "expected no overlaps into variable position"
    (not (any (\cp -> cpRule2 cp == rid2 && cpPosIn2 cp == [0]) cps))

testCriticalPairsSelfOverlapFreshening :: Assertion
testCriticalPairsSelfOverlapFreshening = do
  let rid = RuleId "self" DirLR
  let x = V (Ns rid 0) 0
  let r = mkRule "self" 0 (app "f" [TVar x]) (app "g" [TVar x])
  let rs = mkRS [r]
  let cps = filter (\cp -> cpRule1 cp == rid && cpRule2 cp == rid) (criticalPairs CP_All (getRule rs) rs)
  case cps of
    [] -> assertFailure "expected self-overlap critical pair"
    (cp : _) ->
      case cpMgu cp of
        Subst subst ->
          case M.toList subst of
            [(v0, TVar v1)] -> do
              assertBool "expected freshened namespaces"
                ( (vNs v0 == Ns rid 0 && vNs v1 == Ns rid 1)
                    || (vNs v0 == Ns rid 1 && vNs v1 == Ns rid 0)
                )
            _ -> assertFailure "unexpected MGU shape for self-overlap"

testCriticalPairsCPModeFiltering :: Assertion
testCriticalPairsCPModeFiltering = do
  let ridS1 = RuleId "s1" DirLR
  let ridS2 = RuleId "s2" DirLR
  let ridC1 = RuleId "c1" DirLR
  let x1 = V (Ns ridS1 0) 0
  let x2 = V (Ns ridS2 0) 0
  let x3 = V (Ns ridC1 0) 0
  let rS1 = mkRuleWith Structural "s1" 0 (app "f" [TVar x1]) (app "g" [TVar x1])
  let rS2 = mkRuleWith Structural "s2" 1 (app "f" [TVar x2]) (app "h" [TVar x2])
  let rC1 = mkRuleWith Computational "c1" 2 (app "f" [TVar x3]) (app "k" [TVar x3])
  let rs = mkRS [rS1, rS2, rC1]
  let cls r = ruleClass (getRule rs r)
  let pairIs cls1 cls2 cp = cls (cpRule1 cp) == cls1 && cls (cpRule2 cp) == cls2
  let cpsStructural = criticalPairs CP_OnlyStructural (getRule rs) rs
  assertBool "expected only structural pairs"
    (not (null cpsStructural) && all (\cp -> pairIs Structural Structural cp) cpsStructural)
  let cpsMixed = criticalPairs CP_StructuralVsComputational (getRule rs) rs
  assertBool "expected only mixed pairs"
    (not (null cpsMixed) && all (\cp -> pairIs Structural Computational cp || pairIs Computational Structural cp) cpsMixed)

testCriticalPairSoundness :: Assertion
testCriticalPairSoundness = do
  let rid1 = RuleId "r1" DirLR
  let rid2 = RuleId "r2" DirLR
  let x = V (Ns rid1 0) 0
  let y = V (Ns rid2 0) 0
  let r1 = mkRule "r1" 0 (app "f" [TVar x]) (app "g" [TVar x])
  let r2 = mkRule "r2" 1 (app "h" [app "f" [TVar y]]) (app "k" [TVar y])
  let rs = mkRS [r1, r2]
  let cps = criticalPairs CP_All (getRule rs) rs
  case find (\cp -> cpRule1 cp == rid1 && cpRule2 cp == rid2 && cpPosIn2 cp == [0]) cps of
    Nothing -> assertFailure "expected critical pair at position [0]"
    Just cp -> do
      let r1' = renameRuleNs (Ns rid1 0) r1
      let r2' = renameRuleNs (Ns rid2 1) r2
      let lookupRenamed rid
            | rid == rid1 = r1'
            | rid == rid2 = r2'
            | otherwise = error "unknown rule id"
      applyStep lookupRenamed (Step rid1 (cpPosIn2 cp) (cpMgu cp)) (cpPeak cp) @?= Just (cpLeft cp)
      applyStep lookupRenamed (Step rid2 [] (cpMgu cp)) (cpPeak cp) @?= Just (cpRight cp)

testRewriteOncePositionOrder :: Assertion
testRewriteOncePositionOrder = do
  let rule = mkRule "a" 0 (constTerm "a") (constTerm "b")
  let rs = mkRS [rule]
  let term = app "f" [constTerm "a", constTerm "a"]
  let reds = rewriteOnce rs term
  map (stepPos . redexStep) reds @?= [[0], [1]]

testRewriteOncePositionOrderDeep :: Assertion
testRewriteOncePositionOrderDeep = do
  let rid = RuleId "var" DirLR
  let x = V (Ns rid 0) 0
  let rule = mkRule "var" 0 (TVar x) (TVar x)
  let rs = mkRS [rule]
  let term = app "f" [app "g" [constTerm "a", constTerm "b"], constTerm "c"]
  let reds = rewriteOnce rs term
  map (stepPos . redexStep) reds @?= [[], [0], [0, 0], [0, 1], [1]]

testRewriteOnceRuleOrder :: Assertion
testRewriteOnceRuleOrder = do
  let rid1 = RuleId "r1" DirLR
  let rid2 = RuleId "r2" DirLR
  let x1 = V (Ns rid1 0) 0
  let y1 = V (Ns rid1 0) 1
  let x2 = V (Ns rid2 0) 0
  let r1 = mkRule "r1" 0 (app "f" [TVar x1, TVar y1]) (TVar x1)
  let r2 = mkRule "r2" 1 (app "g" [TVar x2]) (TVar x2)
  let rs = mkRS [r1, r2]
  let term = app "f" [app "g" [constTerm "a"], constTerm "a"]
  let reds = rewriteOnce rs term
  map (stepRule . redexStep) reds @?= [rid1, rid2]

testRewriteOnceRuleOrderSamePos :: Assertion
testRewriteOnceRuleOrderSamePos = do
  let rid1 = RuleId "r1" DirLR
  let rid2 = RuleId "r2" DirLR
  let x1 = V (Ns rid1 0) 0
  let x2 = V (Ns rid2 0) 0
  let r1 = mkRule "r1" 0 (app "f" [TVar x1]) (app "g" [TVar x1])
  let r2 = mkRule "r2" 1 (app "f" [TVar x2]) (app "h" [TVar x2])
  let rs = mkRS [r1, r2]
  let term = app "f" [constTerm "a"]
  let reds = rewriteOnce rs term
  map (stepRule . redexStep) reds @?= [rid1, rid2]

testNormalizeChoosesFirstRule :: Assertion
testNormalizeChoosesFirstRule = do
  let r1 = mkRule "r1" 0 (constTerm "a") (constTerm "b")
  let r2 = mkRule "r2" 1 (constTerm "a") (constTerm "c")
  let rs = mkRS [r1, r2]
  normalize 1 rs (constTerm "a") @?= constTerm "b"

testNormalizeFuelEdgeCases :: Assertion
testNormalizeFuelEdgeCases = do
  let r1 = mkRule "r1" 0 (constTerm "a") (constTerm "b")
  let r2 = mkRule "r2" 1 (constTerm "b") (constTerm "c")
  let rs = mkRS [r1, r2]
  normalize 0 rs (constTerm "a") @?= constTerm "a"
  normalize 1 rs (constTerm "a") @?= constTerm "b"
  normalize 2 rs (constTerm "a") @?= constTerm "c"
