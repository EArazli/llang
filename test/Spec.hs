{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.List (find)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Meta.Coherence
import Strat.Meta.CriticalPairs
import Strat.Meta.DSL.Elab.FO
import Strat.Meta.DoctrineExpr
import Strat.Meta.Examples.Monoid
import Strat.Meta.Presentation
import Strat.Meta.Rewrite
import Strat.Meta.RewriteSystem hiding (mkRule)
import Strat.Meta.Rule
import Strat.Meta.Term.Class
import Strat.Meta.Term.FO
import Strat.Meta.Types
import qualified Strat.Kernel.Syntax as KSyn
import qualified Strat.Kernel.Signature as KSig
import qualified Strat.Kernel.Subst as KSubst
import qualified Strat.Kernel.Term as KTerm
import qualified Strat.Kernel.Unify as KUnify
import qualified Strat.Kernel.Examples.Monoid as KMono
import qualified Strat.Kernel.RewriteSystem as KRS
import qualified Strat.Kernel.CriticalPairs as KCP
import qualified Strat.Kernel.Coherence as KCo
import qualified Strat.Kernel.Rewrite as KRew

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "Strat.Meta"
    [ testGroup
        "Meta"
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
    , testGroup
        "DoctrineExpr"
        [ testCase "disjoint composition qualifies" testDoctrineDisjointQualifies
        , testCase "disjoint rules do not cross-apply" testDoctrineDisjointNoCross
        , testCase "sharing enables cross-application" testDoctrineShareSyms
        , testCase "extends-like same namespace" testDoctrineExtendsLike
        , testCase "duplicate eq names rejected" testDoctrineDuplicateEqNames
        , testCase "rename eqs resolves collisions" testDoctrineRenameEqs
        , testCase "ShareSyms unknown symbol fails" testDoctrineShareUnknown
        , testCase "RenameSyms works" testDoctrineRenameSyms
        ]
    , testGroup
        "DoctrineDSL"
        [ testCase "load succeeds" testDSLLoad
        , testCase "AB disjoint" testDSLDisjoint
        , testCase "ABshared enables cross-apply" testDSLShared
        , testCase "Base@C & Ext@C works" testDSLExtendsLike
        , testCase "Cbad duplicate eq names fails" testDSLDuplicateEqNames
        , testCase "rename syms works" testDSLRenameSyms
        , testCase "share unknown symbol fails" testDSLShareUnknown
        , testCase "RL orientation parses" testDSLRLOrientation
        , testCase "associativity preserves order" testDSLAssocOrdering
        , testCase "share precedence" testDSLSharePrecedence
        ]
    , testGroup
        "Kernel"
        [ testCase "Kernel.Syntax loads" testKernelSyntaxLoads
        , testCase "Kernel.mkOp sanity" testKernelMkOp
        , testCase "Kernel.mkSort sanity" testKernelMkSortSanity
        , testCase "Kernel.mkSort arity mismatch" testKernelMkSortArity
        , testCase "Kernel.mkSort sort mismatch" testKernelMkSortMismatch
        , testCase "Kernel.applySubstSort substitutes indices" testKernelApplySubstSort
        , testCase "Kernel.unify respects sort indices" testKernelUnifySortIndices
        , testCase "Kernel rewriteOnce monoid unit" testKernelRewriteOnceMonoid
        , testCase "Kernel monoid critical pairs" testKernelMonoidCriticalPairs
        , testCase "Kernel monoid obligations" testKernelMonoidObligations
        ]
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

qname :: Text -> Text -> Text
qname nsName x = nsName <> "." <> x

termSym :: Term -> Maybe Text
termSym (TApp (Sym s) _) = Just s
termSym _ = Nothing

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

expectCPs :: CPMode -> RewriteSystem Term -> IO [CriticalPair Term]
expectCPs mode rs =
  case criticalPairs mode (getRule rs) rs of
    Left err -> do
      _ <- assertFailure (show err)
      pure []
    Right cps -> pure cps

presA :: Presentation Term
presA =
  Presentation
    { presName = "A"
    , presEqs =
        [ mkEq "r" Computational LR (app "f" [varX]) (app "g" [varX])
        ]
    }

presB :: Presentation Term
presB =
  Presentation
    { presName = "B"
    , presEqs =
        [ mkEq "r" Computational LR (app "f" [varX]) (app "h" [varX])
        ]
    }

presBase :: Presentation Term
presBase =
  Presentation
    { presName = "Base"
    , presEqs =
        [ mkEq "base" Computational LR (app "f" [varX]) varX
        ]
    }

presExt :: Presentation Term
presExt =
  Presentation
    { presName = "Ext"
    , presEqs =
        [ mkEq "ext" Computational LR (app "k" [app "f" [varX]]) varX
        ]
    }

varX :: Term
varX = TVar (V (ns "v") 0)

testKernelSyntaxLoads :: Assertion
testKernelSyntaxLoads = do
  let obj = KSyn.SortName "Obj"
  let scope = KSyn.ScopeId "ex:Kernel"
  let v0 = KSyn.Var scope 0
  let s = KSyn.Sort obj []
  let t = KTerm.mkVar s v0
  KSyn.termSort t @?= s

kernelSig :: KSig.Signature
kernelSig =
  KSig.Signature
    { KSig.sigSortCtors =
        M.fromList
          [ (objName, KSig.SortCtor objName [])
          , (homName, KSig.SortCtor homName [objSort0, objSort0])
          ]
    , KSig.sigOps = M.fromList [(eName, eDecl), (mName, mDecl)]
    }
  where
    objName = KSyn.SortName "Obj"
    homName = KSyn.SortName "Hom"
    objSort0 = KSyn.Sort objName []
    eName = KSyn.OpName "e"
    mName = KSyn.OpName "m"
    eDecl = KSig.OpDecl eName [] objSort0
    mDecl =
      let scope = KSyn.ScopeId "op:m"
          a = KSyn.Var scope 0
          b = KSyn.Var scope 1
      in KSig.OpDecl mName [KSyn.Binder a objSort0, KSyn.Binder b objSort0] objSort0

objSort :: KSyn.Sort
objSort = KSyn.Sort (KSyn.SortName "Obj") []

homSort :: KSyn.Term -> KSyn.Term -> KSyn.Sort
homSort a b = KSyn.Sort (KSyn.SortName "Hom") [a, b]

kernelE :: KSyn.Term
kernelE =
  case KTerm.mkOp kernelSig (KSyn.OpName "e") [] of
    Left err -> error (show err)
    Right t -> t

testKernelMkOp :: Assertion
testKernelMkOp = do
  let scope = KSyn.ScopeId "ex:Kernel"
  let x = KTerm.mkVar objSort (KSyn.Var scope 0)
  case KTerm.mkOp kernelSig (KSyn.OpName "m") [kernelE, x] of
    Left err -> assertFailure (show err)
    Right t -> KSyn.termSort t @?= objSort

testKernelMkSortSanity :: Assertion
testKernelMkSortSanity =
  case KSig.mkSort kernelSig (KSyn.SortName "Hom") [kernelE, kernelE] of
    Left err -> assertFailure (show err)
    Right s -> s @?= homSort kernelE kernelE

testKernelMkSortArity :: Assertion
testKernelMkSortArity =
  case KSig.mkSort kernelSig (KSyn.SortName "Hom") [kernelE] of
    Left (KSig.SortArityMismatch _ 2 1) -> pure ()
    Left err -> assertFailure ("unexpected error: " <> show err)
    Right _ -> assertFailure "expected arity mismatch"

testKernelMkSortMismatch :: Assertion
testKernelMkSortMismatch = do
  let scope = KSyn.ScopeId "ex:Kernel"
  let homS =
        case KSig.mkSort kernelSig (KSyn.SortName "Hom") [kernelE, kernelE] of
          Left err -> error (show err)
          Right s -> s
  let badIdx = KTerm.mkVar homS (KSyn.Var scope 9)
  case KSig.mkSort kernelSig (KSyn.SortName "Hom") [badIdx, kernelE] of
    Left (KSig.SortIndexSortMismatch _ 0 _ _) -> pure ()
    Left err -> assertFailure ("unexpected error: " <> show err)
    Right _ -> assertFailure "expected sort mismatch"

testKernelApplySubstSort :: Assertion
testKernelApplySubstSort = do
  let scope = KSyn.ScopeId "ex:Kernel"
  let vx = KSyn.Var scope 0
  let x = KTerm.mkVar objSort vx
  let s = homSort x x
  let subst = M.fromList [(vx, kernelE)]
  KSubst.applySubstSort subst s @?= homSort kernelE kernelE

testKernelUnifySortIndices :: Assertion
testKernelUnifySortIndices = do
  let scope = KSyn.ScopeId "ex:Kernel"
  let vx = KSyn.Var scope 0
  let vy = KSyn.Var scope 1
  let x = KTerm.mkVar objSort vx
  let y = KTerm.mkVar objSort vy
  let s1 = homSort x y
  let s2 = homSort kernelE kernelE
  let t1 = KSyn.Term { KSyn.termSort = s1, KSyn.termNode = KSyn.TVar (KSyn.Var scope 2) }
  let t2 = KSyn.Term { KSyn.termSort = s2, KSyn.termNode = KSyn.TVar (KSyn.Var scope 3) }
  case KUnify.unify t1 t2 of
    Nothing -> assertFailure "expected unifier"
    Just subst -> do
      KSubst.applySubstSort subst (KSyn.termSort t1) @?= KSubst.applySubstSort subst (KSyn.termSort t2)
      KSubst.applySubstTerm subst x @?= kernelE
      KSubst.applySubstTerm subst y @?= kernelE

testKernelRewriteOnceMonoid :: Assertion
testKernelRewriteOnceMonoid =
  case KRS.compileRewriteSystem KRS.UseOnlyComputationalLR KMono.presMonoid of
    Left err -> assertFailure (T.unpack err)
    Right rs ->
      case (KMono.eTerm, KMono.eTerm) of
        (Right e, Right e2) ->
          case KMono.mTerm e e2 of
            Left err -> assertFailure (show err)
            Right term ->
              case KRew.rewriteOnce rs term of
                [redex] -> KRew.redexTo redex @?= e
                reds -> assertFailure ("expected single redex, got " <> show (length reds))
        _ -> assertFailure "failed to build monoid terms"

testKernelMonoidCriticalPairs :: Assertion
testKernelMonoidCriticalPairs =
  case KRS.compileRewriteSystem KRS.UseOnlyComputationalLR KMono.presMonoid of
    Left err -> assertFailure (T.unpack err)
    Right rs ->
      case KCP.criticalPairs KCP.CP_All (KRS.getRule rs) rs of
        Left err -> assertFailure (T.unpack err)
        Right cps -> assertBool "expected non-empty critical pairs" (not (null cps))

testKernelMonoidObligations :: Assertion
testKernelMonoidObligations =
  case KRS.compileRewriteSystem KRS.UseOnlyComputationalLR KMono.presMonoid of
    Left err -> assertFailure (T.unpack err)
    Right rs ->
      case KCP.criticalPairs KCP.CP_All (KRS.getRule rs) rs of
        Left err -> assertFailure (T.unpack err)
        Right cps ->
          let obs = KCo.obligationsFromCPs cps
          in assertBool "expected obligations from critical pairs" (not (null obs))

dslProgram :: Text
dslProgram =
  T.unlines
    [ "doctrine A where {"
    , "  computational r : f(?x) -> g(?x);"
    , "}"
    , ""
    , "doctrine B where {"
    , "  computational r : f(?x) -> h(?x);"
    , "}"
    , ""
    , "doctrine AB = A & B;"
    , ""
    , "doctrine ABshared = share syms { A.f = B.f } in (A & B);"
    , ""
    , "doctrine Base where {"
    , "  computational base : f(?x) -> ?x;"
    , "}"
    , ""
    , "doctrine Ext where {"
    , "  computational ext : k(f(?x)) -> ?x;"
    , "}"
    , ""
    , "doctrine C = (Base@C) & (Ext@C);"
    , ""
    , "doctrine Cbad = (A@C) & (B@C);"
    , ""
    , "doctrine Aren = rename syms { A.g -> A.g2 } in A;"
    , ""
    , "doctrine BadShare = share syms { A.missing = B.f } in (A & B);"
    , ""
    , "doctrine RLTest where {"
    , "  computational rr : a <- b;"
    , "}"
    , ""
    , "doctrine AssocTest = A & B & Base;"
    , ""
    , "doctrine ABshared2 = share syms { A.f = B.f } in A & B;"
    ]

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
  cps <- expectCPs CP_All rs
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
  cps <- expectCPs CP_All rs
  assertBool "expected no overlaps into variable lhs"
    (all (\cp -> cpRule2 cp /= ridVar) cps)

testCriticalPairsExcludeInnerVarOverlap :: Assertion
testCriticalPairsExcludeInnerVarOverlap = do
  let rid2 = RuleId "r2" DirLR
  let x = V (Ns rid2 0) 0
  let r1 = mkRule "r1" 0 (constTerm "a") (constTerm "b")
  let r2 = mkRule "r2" 1 (app "f" [TVar x]) (app "g" [TVar x])
  let rs = mkRS [r1, r2]
  cps <- expectCPs CP_All rs
  assertBool "expected no overlaps into variable position"
    (not (any (\cp -> cpRule2 cp == rid2 && cpPosIn2 cp == [0]) cps))

testCriticalPairsSelfOverlapFreshening :: Assertion
testCriticalPairsSelfOverlapFreshening = do
  let rid = RuleId "self" DirLR
  let x = V (Ns rid 0) 0
  let r = mkRule "self" 0 (app "f" [TVar x]) (app "g" [TVar x])
  let rs = mkRS [r]
  cpsAll <- expectCPs CP_All rs
  let cps = filter (\cp -> cpRule1 cp == rid && cpRule2 cp == rid) cpsAll
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
  cpsStructural <- expectCPs CP_OnlyStructural rs
  assertBool "expected only structural pairs"
    (not (null cpsStructural) && all (\cp -> pairIs Structural Structural cp) cpsStructural)
  cpsMixed <- expectCPs CP_StructuralVsComputational rs
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
  cps <- expectCPs CP_All rs
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

testDoctrineDisjointQualifies :: Assertion
testDoctrineDisjointQualifies = do
  let expr = And (Atom "A" presA) (Atom "B" presB)
  case elabDocExpr expr of
    Left err -> assertFailure (show err)
    Right p -> do
      map eqName (presEqs p) @?= [qname "A" "r", qname "B" "r"]
      case presEqs p of
        (e1 : e2 : _) -> do
          termSym (eqLHS e1) @?= Just (qname "A" "f")
          termSym (eqLHS e2) @?= Just (qname "B" "f")
        _ -> assertFailure "expected two equations"
      case compileDocExpr UseOnlyComputationalLR expr of
        Left err -> assertFailure (show err)
        Right _ -> pure ()

testDoctrineDisjointNoCross :: Assertion
testDoctrineDisjointNoCross = do
  let expr = And (Atom "A" presA) (Atom "B" presB)
  case compileDocExpr UseOnlyComputationalLR expr of
    Left err -> assertFailure (show err)
    Right rs -> do
      let t = app (qname "A" "f") [constTerm "z"]
      let reds = rewriteOnce rs t
      length reds @?= 1
      map (stepRule . redexStep) reds @?= [RuleId (qname "A" "r") DirLR]

testDoctrineShareSyms :: Assertion
testDoctrineShareSyms = do
  let expr = And (Atom "A" presA) (Atom "B" presB)
  let exprShared = ShareSyms [(qname "A" "f", qname "B" "f")] expr
  case compileDocExpr UseOnlyComputationalLR exprShared of
    Left err -> assertFailure (show err)
    Right rs -> do
      let t = app (qname "A" "f") [constTerm "z"]
      let reds = rewriteOnce rs t
      length reds @?= 2
      map (stepRule . redexStep) reds
        @?= [ RuleId (qname "A" "r") DirLR
            , RuleId (qname "B" "r") DirLR
            ]

testDoctrineExtendsLike :: Assertion
testDoctrineExtendsLike = do
  let exprExt = And (Atom "C" presBase) (Atom "C" presExt)
  case compileDocExpr UseOnlyComputationalLR exprExt of
    Left err -> assertFailure (show err)
    Right rs -> do
      let t = app (qname "C" "k") [app (qname "C" "f") [constTerm "z"]]
      normalize 1 rs t @?= constTerm "z"

testDoctrineDuplicateEqNames :: Assertion
testDoctrineDuplicateEqNames = do
  let exprDup = And (Atom "C" presA) (Atom "C" presB)
  case elabDocExpr exprDup of
    Left _ -> pure ()
    Right _ -> assertFailure "expected duplicate equation name rejection"

testDoctrineRenameEqs :: Assertion
testDoctrineRenameEqs = do
  let exprFixed =
        And
          (Atom "C" presA)
          (RenameEqs (M.fromList [(qname "C" "r", qname "C" "r2")]) (Atom "C" presB))
  case compileDocExpr UseOnlyComputationalLR exprFixed of
    Left err -> assertFailure (show err)
    Right rs -> do
      let rules = map ruleId (rsRules rs)
      assertBool "expected C.r rule" (RuleId (qname "C" "r") DirLR `elem` rules)
      assertBool "expected C.r2 rule" (RuleId (qname "C" "r2") DirLR `elem` rules)

testDoctrineShareUnknown :: Assertion
testDoctrineShareUnknown = do
  let expr = And (Atom "A" presA) (Atom "B" presB)
  let exprBad = ShareSyms [(qname "A" "missing", qname "B" "f")] expr
  case elabDocExpr exprBad of
    Left _ -> pure ()
    Right _ -> assertFailure "expected ShareSyms unknown symbol failure"

testDoctrineRenameSyms :: Assertion
testDoctrineRenameSyms = do
  let expr = RenameSyms (M.fromList [(qname "A" "g", qname "A" "g2")]) (Atom "A" presA)
  case elabDocExpr expr of
    Left err -> assertFailure (show err)
    Right p ->
      case presEqs p of
        (e1 : _) -> termSym (eqRHS e1) @?= Just (qname "A" "g2")
        _ -> assertFailure "expected at least one equation"

testDSLLoad :: Assertion
testDSLLoad =
  case loadDoctrinesFO dslProgram of
    Left err -> assertFailure (show err)
    Right env -> do
      let expected =
            [ "A", "B", "AB", "ABshared", "Base", "Ext", "C", "Cbad"
            , "Aren", "BadShare", "RLTest", "AssocTest", "ABshared2"
            ]
      assertBool "expected all doctrine keys"
        (all (`M.member` env) expected)

testDSLDisjoint :: Assertion
testDSLDisjoint = do
  env <- requireEnv
  expr <- requireExpr env "AB"
  case compileDocExpr UseOnlyComputationalLR expr of
    Left err -> assertFailure (show err)
    Right rs -> do
      let t = app (qname "A" "f") [constTerm "z"]
      let reds = rewriteOnce rs t
      length reds @?= 1
      map (stepRule . redexStep) reds @?= [RuleId (qname "A" "r") DirLR]

testDSLShared :: Assertion
testDSLShared = do
  env <- requireEnv
  expr <- requireExpr env "ABshared"
  case compileDocExpr UseOnlyComputationalLR expr of
    Left err -> assertFailure (show err)
    Right rs -> do
      let t = app (qname "A" "f") [constTerm "z"]
      let reds = rewriteOnce rs t
      length reds @?= 2
      map (stepRule . redexStep) reds
        @?= [ RuleId (qname "A" "r") DirLR
            , RuleId (qname "B" "r") DirLR
            ]

testDSLExtendsLike :: Assertion
testDSLExtendsLike = do
  env <- requireEnv
  expr <- requireExpr env "C"
  case compileDocExpr UseOnlyComputationalLR expr of
    Left err -> assertFailure (show err)
    Right rs -> do
      let t = app (qname "C" "k") [app (qname "C" "f") [constTerm "z"]]
      normalize 1 rs t @?= constTerm "z"

testDSLDuplicateEqNames :: Assertion
testDSLDuplicateEqNames = do
  env <- requireEnv
  expr <- requireExpr env "Cbad"
  case elabDocExpr expr of
    Left _ -> pure ()
    Right _ -> assertFailure "expected duplicate eq name failure"

testDSLRenameSyms :: Assertion
testDSLRenameSyms = do
  env <- requireEnv
  expr <- requireExpr env "Aren"
  case elabDocExpr expr of
    Left err -> assertFailure (show err)
    Right p ->
      case presEqs p of
        (e1 : _) -> termSym (eqRHS e1) @?= Just (qname "A" "g2")
        _ -> assertFailure "expected at least one equation"

testDSLShareUnknown :: Assertion
testDSLShareUnknown = do
  env <- requireEnv
  expr <- requireExpr env "BadShare"
  case elabDocExpr expr of
    Left _ -> pure ()
    Right _ -> assertFailure "expected unknown symbol failure"

testDSLRLOrientation :: Assertion
testDSLRLOrientation = do
  env <- requireEnv
  expr <- requireExpr env "RLTest"
  case compileDocExpr UseAllOriented expr of
    Left err -> assertFailure (show err)
    Right rs ->
      case rsRules rs of
        [r] -> ruleId r @?= RuleId (qname "RLTest" "rr") DirRL
        _ -> assertFailure "expected one RL rule"

testDSLAssocOrdering :: Assertion
testDSLAssocOrdering = do
  env <- requireEnv
  expr <- requireExpr env "AssocTest"
  case elabDocExpr expr of
    Left err -> assertFailure (show err)
    Right p ->
      map eqName (presEqs p)
        @?= [qname "A" "r", qname "B" "r", qname "Base" "base"]

testDSLSharePrecedence :: Assertion
testDSLSharePrecedence = do
  env <- requireEnv
  expr <- requireExpr env "ABshared2"
  case compileDocExpr UseOnlyComputationalLR expr of
    Left err -> assertFailure (show err)
    Right rs -> do
      let t = app (qname "A" "f") [constTerm "z"]
      let reds = rewriteOnce rs t
      length reds @?= 2
      map (stepRule . redexStep) reds
        @?= [ RuleId (qname "A" "r") DirLR
            , RuleId (qname "B" "r") DirLR
            ]

requireEnv :: IO (M.Map Text (DocExpr Term))
requireEnv =
  case loadDoctrinesFO dslProgram of
    Left err -> do
      _ <- assertFailure (show err)
      pure M.empty
    Right env -> pure env

requireExpr :: M.Map Text (DocExpr Term) -> Text -> IO (DocExpr Term)
requireExpr env name =
  case M.lookup name env of
    Nothing -> do
      _ <- assertFailure ("missing doctrine: " <> T.unpack name)
      pure (Atom "Missing" (Presentation "Missing" []))
    Just expr -> pure expr
