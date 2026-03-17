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
import Strat.Poly.Obj
import Strat.Poly.Names
import Strat.Poly.Diagram
import Strat.Poly.DiagramIso (diagramIsoEq)
import Strat.Poly.Graph
  ( BinderArg(..)
  , BinderMetaVar(..)
  , Edge(..)
  , EdgePayload(..)
  , addEdgePayload
  , diagramPortObj
  , emptyDiagram
  , freshPort
  , validateDiagram
  )
import Strat.Poly.Rewrite (RewriteRule(..))
import Strat.Poly.CriticalPairs
import Strat.Poly.CriticalPairsDoctrine (criticalPairsForDoctrine)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), InputShape(..), validateDoctrine)
import Strat.Common.Rules (RewritePolicy(..), Orientation(..))
import Strat.Poly.DefEq (normalizeTermDiagram)
import Strat.Poly.TypeTheory
  ( TypeTheory
  , BinderSig(..)
  , TmHeadSig(..)
  , modeOnlyTypeTheory
  , setModeTermHeads
  )
import Test.Poly.Helpers (mkModes, withZeroParamGenArgSigs)


tests :: TestTree
tests =
  testGroup
    "Poly.CriticalPairs"
    [ testCase "critical pairs respect mode equations in overlap matching" testCriticalPairsRespectModeEq
    , testCase "critical pairs freshen colliding type variable names across rules" testCriticalPairsFreshenTyVars
    , testCase "critical pairs fail when dependent substitution fails" testCriticalPairsFailOnSubstFailure
    , testCase "critical pairs include binder-hole nested overlaps" testCriticalPairsIncludeBinderHoleOverlap
    , testCase "fragment confluence catches root overlaps through alpha-equivalent binder payloads" testFragmentConfluenceRootBinderOverlap
    , testCase "critical pairs include root overlaps between binder holes and concrete bodies" testCriticalPairsIncludeRootBinderHoleOverlap
    , testCase "critical pairs use modality action mapping in nested overlaps" testCriticalPairsUseActionMappingInNestedOverlaps
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
  let baseTy = mkCon (ObjRef mode (ObjName "Base")) []
  let ufBaseTy = OMod uExpr (OMod fExpr baseTy)
  let mt =
        ModeTheory
          { mtModes = M.singleton mode (ModeInfo { miName = mode })
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
          , mtTransforms = M.empty
          , mtClassifiedBy = M.empty
          , mtClassifierLifts = M.empty
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
  assertBool "expected cross-rule overlap under U.F -> mode equation" (not (null pairs))

testCriticalPairsFreshenTyVars :: Assertion
testCriticalPairsFreshenTyVars = do
  let mode = ModeName "M"
  let a = mkModeMetaVar "a" mode
  let baseTy = mkCon (ObjRef mode (ObjName "B")) []
  g1 <- require (genD mode [baseTy] [baseTy] (GenName "g"))
  h1 <- require (genD mode [OVar a] [OVar a] (GenName "h1"))
  lhs1 <- require (tensorD g1 h1)
  g2 <- require (genD mode [baseTy] [baseTy] (GenName "g"))
  h2 <- require (genD mode [OVar a] [OVar a] (GenName "h2"))
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
  assertBool "expected overlap to keep distinct tyvars from both rules" (any (\d -> S.size (freeVarsDiagram d) >= 2) cross)

testCriticalPairsFailOnSubstFailure :: Assertion
testCriticalPairsFailOnSubstFailure = do
  let mode = ModeName "M"
  let aTy = mkCon (ObjRef mode (ObjName "A")) []
  let badTmSort = mkCon (ObjRef mode (ObjName "BadSort")) [OAObj aTy]
  lhs <- require (genDTm mode [badTmSort] [aTy] [aTy] (GenName "g"))
  let cell =
        Cell2
          { c2Name = "bad-subst"
          , c2Class = Structural
          , c2Orient = LR
          , c2Params = []
          , c2LHS = lhs
          , c2RHS = lhs
          }
  let doc =
        Doctrine
          { dName = "D"
          , dModes =
              (mkModes [mode])
                { mtClassifiedBy =
                    M.singleton
                      mode
                      ClassificationDecl
                        { cdClassifier = mode
                        , cdUniverse = mkCon (ObjRef mode (ObjName "U")) []
                        
                        , cdComp =
                            Just
                              CompDecl
                                { compCtxExt = GenName "comp_ctx_ext"
                                , compVar = GenName "comp_var"
                                , compReindex = GenName "comp_reindex"
                                }
                        }
                }
          , dAcyclicModes = S.empty
                    , dGens =
              M.singleton
                mode
                ( M.fromList
                    [ ( GenName "A"
                      , GenDecl
                          { gdName = GenName "A"
                          , gdMode = mode
                          , gdParams = []
                          , gdDom = []
                          , gdCod = [mkCon (ObjRef mode (ObjName "U")) []]
                          , gdLiteralKind = Nothing
                          }
                      )
                    , ( GenName "comp_ctx_ext"
                      , GenDecl
                          { gdName = GenName "comp_ctx_ext"
                          , gdMode = mode
                          , gdParams = []
                          , gdDom = [InPort (mkCon (ObjRef mode (ObjName "U")) [])]
                          , gdCod = [mkCon (ObjRef mode (ObjName "U")) []]
                          , gdLiteralKind = Nothing
                          }
                      )
                    , ( GenName "comp_var"
                      , GenDecl
                          { gdName = GenName "comp_var"
                          , gdMode = mode
                          , gdParams = []
                          , gdDom = [InPort (mkCon (ObjRef mode (ObjName "U")) [])]
                          , gdCod = [mkCon (ObjRef mode (ObjName "U")) []]
                          , gdLiteralKind = Nothing
                          }
                      )
                    , ( GenName "comp_reindex"
                      , GenDecl
                          { gdName = GenName "comp_reindex"
                          , gdMode = mode
                          , gdParams = []
                          , gdDom = [InPort (mkCon (ObjRef mode (ObjName "U")) [])]
                          , gdCod = [mkCon (ObjRef mode (ObjName "U")) []]
                          , gdLiteralKind = Nothing
                          }
                      )
                    ]
                )
          , dCells2 = [cell]
          , dBuiltins = []
          , dActions = M.empty
          , dObligations = []
          }
  _ <- require (validateDoctrine doc)
  case criticalPairsForDoctrine CP_All UseAllOriented doc of
    Left err -> assertBool "expected substitution-failure error" ("substitution failure" `T.isInfixOf` err)
    Right _ -> assertFailure "expected critical pair generation to fail"

testCriticalPairsIncludeBinderHoleOverlap :: Assertion
testCriticalPairsIncludeBinderHoleOverlap = do
  let mode = ModeName "M"
  let aTy = mkCon (ObjRef mode (ObjName "A")) []
  betaLHS <- requireStep "betaLHS" (mkBetaInput mode aTy (BAMeta (BinderMetaVar "Body")))
  betaRHS <- requireStep "betaRHS" (mkSpliceRHS mode aTy (BinderMetaVar "Body"))
  baseTT <- requireStep "baseTT" (withZeroParamGenArgSigs [betaLHS, betaRHS] (modeOnlyTypeTheory (mkModes [mode])))
  keep <- requireStep "keep" (genD mode [aTy] [aTy] (GenName "keep"))
  bad <- requireStep "bad" (genD mode [aTy] [aTy] (GenName "bad"))
  let bodyLHS = keep
  let bodyRHS = bad
  tt0 <- requireStep "tt0" (withZeroParamGenArgSigs [bodyLHS, bodyRHS] baseTT)
  let lamSig =
        TmHeadSig
          { thsParams = []
          , thsInputs = []
          , thsBinders = [BinderSig { bsTmCtx = [], bsDom = [aTy], bsCod = [aTy] }]
          , thsRes = aTy
          }
      tt =
        setModeTermHeads
          mode
          (M.fromList [(GenName "lam", lamSig)])
          tt0
      betaInfo =
        RuleInfo
          { riLabel = "beta"
          , riRule = RewriteRule { rrName = "beta", rrLHS = betaLHS, rrRHS = betaRHS, rrTyVars = [], rrTmVars = [] }
          , riClass = Computational
          }
      bodyInfo =
        RuleInfo
          { riLabel = "body"
          , riRule = RewriteRule { rrName = "body", rrLHS = bodyLHS, rrRHS = bodyRHS, rrTyVars = [], rrTmVars = [] }
          , riClass = Computational
          }
  pairs <- require (criticalPairsForRulesInTypeTheory tt CP_All [betaInfo, bodyInfo])
  let cross =
        [ cpiPair info
        | info <- pairs
        , let pair = cpiPair info
        , cpRule1 pair == "beta"
        , cpRule2 pair == "body"
        ]
  assertBool "expected beta/body binder-hole overlap critical pair" (not (null cross))

testFragmentConfluenceRootBinderOverlap :: Assertion
testFragmentConfluenceRootBinderOverlap = do
  let mode = ModeName "M"
      aTy = mkCon (ObjRef mode (ObjName "A")) []
      scopeSig =
        TmHeadSig
          { thsParams = []
          , thsInputs = []
          , thsBinders = [BinderSig { bsTmCtx = [], bsDom = [aTy], bsCod = [aTy] }]
          , thsRes = aTy
          }
      constSig =
        TmHeadSig
          { thsParams = []
          , thsInputs = []
          , thsBinders = []
          , thsRes = aTy
          }
  bodyL <- requireStep "bodyL" (mkIdentityBinderBody mode aTy)
  bodyR0 <- requireStep "bodyR0" (mkIdentityBinderBody mode aTy)
  let bodyR = bodyR0 { dNextPort = dNextPort bodyR0 + 7, dNextEdge = dNextEdge bodyR0 + 3 }
  assertBool "expected binder bodies to differ structurally while remaining alpha-equivalent" (bodyL /= bodyR)
  lhsL <- requireStep "lhsL" (mkNullaryBinderHead mode aTy (GenName "scope") bodyL)
  lhsR <- requireStep "lhsR" (mkNullaryBinderHead mode aTy (GenName "scope") bodyR)
  rhsKeep <- requireStep "rhsKeep" (genD mode [] [aTy] (GenName "keep"))
  rhsBad <- requireStep "rhsBad" (genD mode [] [aTy] (GenName "bad"))
  tt0 <- requireStep "tt0" (withZeroParamGenArgSigs [lhsL, lhsR, rhsKeep, rhsBad] (modeOnlyTypeTheory (mkModes [mode])))
  let tt =
        setModeTermHeads
          mode
          (M.fromList [(GenName "scope", scopeSig), (GenName "keep", constSig), (GenName "bad", constSig)])
          tt0
      leftInfo =
        RuleInfo
          { riLabel = "scope.keep"
          , riRule = RewriteRule { rrName = "scope.keep", rrLHS = lhsL, rrRHS = rhsKeep, rrTyVars = [], rrTmVars = [] }
          , riClass = Computational
          }
      rightInfo =
        RuleInfo
          { riLabel = "scope.bad"
          , riRule = RewriteRule { rrName = "scope.bad", rrLHS = lhsR, rrRHS = rhsBad, rrTyVars = [], rrTmVars = [] }
          , riClass = Computational
          }
  pairs <- requireStep "pairs" (criticalPairsForRulesInTypeTheory tt CP_All [leftInfo, rightInfo])
  let rootPairs =
        [ cpiPair info
        | info <- pairs
        , let pair = cpiPair info
        , (cpRule1 pair == "scope.keep" && cpRule2 pair == "scope.bad")
            || (cpRule1 pair == "scope.bad" && cpRule2 pair == "scope.keep")
        ]
  assertBool "expected root critical pair through alpha-equivalent binder payloads" (not (null rootPairs))
  let pair = head rootPairs
  leftNF <- requireStep "leftNF" (normalizeRootPairSide tt (cpLeft pair))
  rightNF <- requireStep "rightNF" (normalizeRootPairSide tt (cpRight pair))
  same <- requireStep "iso" (diagramIsoEq leftNF rightNF)
  assertBool "expected root binder-overlap branches to remain non-joinable" (not same)

testCriticalPairsIncludeRootBinderHoleOverlap :: Assertion
testCriticalPairsIncludeRootBinderHoleOverlap = do
  let mode = ModeName "M"
      aTy = mkCon (ObjRef mode (ObjName "A")) []
      hole = BinderMetaVar "Body"
      scopeSig =
        TmHeadSig
          { thsParams = []
          , thsInputs = []
          , thsBinders = [BinderSig { bsTmCtx = [], bsDom = [aTy], bsCod = [aTy] }]
          , thsRes = aTy
          }
      constSig =
        TmHeadSig
          { thsParams = []
          , thsInputs = []
          , thsBinders = []
          , thsRes = aTy
          }
  body <- requireStep "body" (mkIdentityBinderBody mode aTy)
  lhsMeta <- requireStep "lhsMeta" (mkNullaryBinderMetaHead mode aTy (GenName "scope") hole)
  lhsConcrete <- requireStep "lhsConcrete" (mkNullaryBinderHead mode aTy (GenName "scope") body)
  rhsKeep <- requireStep "rhsKeep" (genD mode [] [aTy] (GenName "keep"))
  rhsBad <- requireStep "rhsBad" (genD mode [] [aTy] (GenName "bad"))
  tt0 <- requireStep "tt0" (withZeroParamGenArgSigs [lhsMeta, lhsConcrete, rhsKeep, rhsBad] (modeOnlyTypeTheory (mkModes [mode])))
  let tt =
        setModeTermHeads
          mode
          (M.fromList [(GenName "scope", scopeSig), (GenName "keep", constSig), (GenName "bad", constSig)])
          tt0
      holeInfo =
        RuleInfo
          { riLabel = "scope.hole"
          , riRule = RewriteRule { rrName = "scope.hole", rrLHS = lhsMeta, rrRHS = rhsKeep, rrTyVars = [], rrTmVars = [] }
          , riClass = Computational
          }
      concreteInfo =
        RuleInfo
          { riLabel = "scope.concrete"
          , riRule = RewriteRule { rrName = "scope.concrete", rrLHS = lhsConcrete, rrRHS = rhsBad, rrTyVars = [], rrTmVars = [] }
          , riClass = Computational
          }
  pairs <- requireStep "pairs" (criticalPairsForRulesInTypeTheory tt CP_All [holeInfo, concreteInfo])
  let rootPairs =
        [ cpiPair info
        | info <- pairs
        , let pair = cpiPair info
        , (cpRule1 pair == "scope.hole" && cpRule2 pair == "scope.concrete")
            || (cpRule1 pair == "scope.concrete" && cpRule2 pair == "scope.hole")
        ]
  assertBool "expected root critical pair between binder hole and concrete body" (not (null rootPairs))
  let pair = head rootPairs
  leftNF <- requireStep "leftNF" (normalizeRootPairSide tt (cpLeft pair))
  rightNF <- requireStep "rightNF" (normalizeRootPairSide tt (cpRight pair))
  same <- requireStep "iso" (diagramIsoEq leftNF rightNF)
  assertBool "expected binder-hole root overlap branches to remain non-joinable" (not same)

testCriticalPairsUseActionMappingInNestedOverlaps :: Assertion
testCriticalPairsUseActionMappingInNestedOverlaps = do
  let mode = ModeName "M"
      box = ModName "Box"
      boxExpr = ModExpr { meSrc = mode, meTgt = mode, mePath = [box] }
      aTy = mkCon (ObjRef mode (ObjName "A")) []
      hole = BinderMetaVar "Body"
      lamSig =
        TmHeadSig
          { thsParams = []
          , thsInputs = []
          , thsBinders = [BinderSig { bsTmCtx = [], bsDom = [aTy], bsCod = [aTy] }]
          , thsRes = aTy
          }
      unarySig =
        TmHeadSig
          { thsParams = []
          , thsInputs = [aTy]
          , thsBinders = []
          , thsRes = aTy
          }
      binarySig =
        TmHeadSig
          { thsParams = []
          , thsInputs = [aTy, aTy]
          , thsBinders = []
          , thsRes = aTy
          }
  innerBody <- requireStep "innerBody" (mkIdentityBinderBody mode aTy)
  innerBeta <- requireStep "innerBeta" (mkBetaInput mode aTy (BAConcrete innerBody))
  betaLHS <- requireStep "betaLHS" (mkBetaInput mode aTy (BAMeta hole))
  betaRHS <- requireStep "betaRHS" (mkSpliceRHSWithMod mode aTy hole boxExpr)
  outerCore <- requireStep "outerCore" (mkBetaInput mode aTy (BAConcrete innerBeta))
  outerLHS <- requireStep "outerLHS" (mkWrapDiagram mode aTy outerCore)
  let outerRHS = idD mode [aTy]
  baseTT <- requireStep "baseTT" (withZeroParamGenArgSigs [betaLHS, betaRHS, outerLHS, outerRHS] (modeOnlyTypeTheory (mkModes [mode])))
  let tt =
        setModeTermHeads
          mode
          ( M.fromList
              [ (GenName "lam", lamSig)
              , (GenName "lamB", lamSig)
              , (GenName "app", binarySig)
              , (GenName "appB", binarySig)
              , (GenName "wrap", unarySig)
              ]
          )
          baseTT
      betaInfo =
        RuleInfo
          { riLabel = "beta_box"
          , riRule = RewriteRule { rrName = "beta_box", rrLHS = betaLHS, rrRHS = betaRHS, rrTyVars = [], rrTmVars = [] }
          , riClass = Computational
          }
      outerInfo =
        RuleInfo
          { riLabel = "outer"
          , riRule = RewriteRule { rrName = "outer", rrLHS = outerLHS, rrRHS = outerRHS, rrTyVars = [], rrTmVars = [] }
          , riClass = Computational
          }
      mapper me captured
        | me == boxExpr = renameLamAppHeads captured
        | otherwise = Left "unexpected splice modality in critical-pair test"
  pairsDefault <- requireStep "pairsDefault" (criticalPairsForRulesInTypeTheory tt CP_All [outerInfo, betaInfo])
  pairsMapped <- requireStep "pairsMapped" (criticalPairsForRulesInTypeTheoryWithMapper tt mapper CP_All [outerInfo, betaInfo])
  let cross pairs =
        [ cpiPair info
        | info <- pairs
        , let pair = cpiPair info
        , (cpRule1 pair == "outer" && cpRule2 pair == "beta_box")
            || (cpRule1 pair == "beta_box" && cpRule2 pair == "outer")
        ]
  assertBool "expected same-mode nested critical-pair generation to miss mapped splice overlap" (null (cross pairsDefault))
  assertBool "expected mapper-aware nested critical-pair generation to find mapped splice overlap" (not (null (cross pairsMapped)))

requireStep :: Text -> Either Text a -> IO a
requireStep label =
  either (\err -> assertFailure (T.unpack (label <> ": " <> err))) pure

mkBetaInput :: ModeName -> Obj -> BinderArg -> Either Text Diagram
mkBetaInput mode aTy lamArg = do
  let (x, d0) = freshPort aTy (emptyDiagram mode [])
  let (lamOut, d1) = freshPort aTy d0
  let (y, d2) = freshPort aTy d1
  d3 <- addEdgePayload (PGen (GenName "lam") [] [lamArg]) [] [lamOut] d2
  d4 <- addEdgePayload (PGen (GenName "app") [] []) [lamOut, x] [y] d3
  let diag = d4 { dIn = [x], dOut = [y] }
  validateDiagram diag
  pure diag

mkSpliceRHS :: ModeName -> Obj -> BinderMetaVar -> Either Text Diagram
mkSpliceRHS mode aTy meta = do
  let (x, d0) = freshPort aTy (emptyDiagram mode [])
  let (y, d1) = freshPort aTy d0
  let me = ModExpr { meSrc = mode, meTgt = mode, mePath = [] }
  d2 <- addEdgePayload (PSplice meta me) [x] [y] d1
  let diag = d2 { dIn = [x], dOut = [y] }
  validateDiagram diag
  pure diag

mkIdentityBinderBody :: ModeName -> Obj -> Either Text Diagram
mkIdentityBinderBody mode aTy = do
  let (x, d0) = freshPort aTy (emptyDiagram mode [])
  let diag = d0 { dIn = [x], dOut = [x] }
  validateDiagram diag
  pure diag

mkNullaryBinderHead :: ModeName -> Obj -> GenName -> Diagram -> Either Text Diagram
mkNullaryBinderHead mode sortTy g body = do
  let (out, d0) = freshPort sortTy (emptyDiagram mode [])
  d1 <- addEdgePayload (PGen g [] [BAConcrete body]) [] [out] d0
  let diag = d1 { dIn = [], dOut = [out] }
  validateDiagram diag
  pure diag

mkNullaryBinderMetaHead :: ModeName -> Obj -> GenName -> BinderMetaVar -> Either Text Diagram
mkNullaryBinderMetaHead mode sortTy g hole = do
  let (out, d0) = freshPort sortTy (emptyDiagram mode [])
  d1 <- addEdgePayload (PGen g [] [BAMeta hole]) [] [out] d0
  let diag = d1 { dIn = [], dOut = [out] }
  validateDiagram diag
  pure diag

normalizeRootPairSide :: TypeTheory -> Diagram -> Either Text Diagram
normalizeRootPairSide tt diag = do
  outPid <-
    case dOut diag of
      [pid] -> Right pid
      _ -> Left "expected single-output root critical-pair branch"
  outTy <-
    case diagramPortObj diag outPid of
      Just ty -> Right ty
      Nothing -> Left "expected root critical-pair branch to carry an output sort"
  term <- normalizeTermDiagram tt (dTmCtx diag) outTy (TermDiagram diag)
  pure (unTerm term)

mkSpliceRHSWithMod :: ModeName -> Obj -> BinderMetaVar -> ModExpr -> Either Text Diagram
mkSpliceRHSWithMod mode aTy meta me = do
  let (x, d0) = freshPort aTy (emptyDiagram mode [])
  let (y, d1) = freshPort aTy d0
  d2 <- addEdgePayload (PSplice meta me) [x] [y] d1
  let diag = d2 { dIn = [x], dOut = [y] }
  validateDiagram diag
  pure diag

mkWrapDiagram :: ModeName -> Obj -> Diagram -> Either Text Diagram
mkWrapDiagram _mode aTy inner = do
  outPid <-
    case dOut inner of
      [pid] -> Right pid
      _ -> Left "mkWrapDiagram: expected single-output input diagram"
  let (out, d0) = freshPort aTy inner
  d1 <- addEdgePayload (PGen (GenName "wrap") [] []) [outPid] [out] d0
  let diag = d1 { dOut = [out] }
  validateDiagram diag
  pure diag

renameLamAppHeads :: Diagram -> Either Text Diagram
renameLamAppHeads = go
  where
    go diag = do
      edges' <- traverse goEdge (dEdges diag)
      pure diag { dEdges = edges' }

    goEdge edge = do
      payload' <- goPayload (ePayload edge)
      pure edge { ePayload = payload' }

    goPayload payload =
      case payload of
        PGen g args bargs -> do
          args' <- mapM goCodeArg args
          bargs' <- mapM goBinderArg bargs
          let g' =
                if g == GenName "lam"
                  then GenName "lamB"
                  else if g == GenName "app"
                    then GenName "appB"
                    else g
          pure (PGen g' args' bargs')
        PBox name inner ->
          PBox name <$> go inner
        PFeedback inner ->
          PFeedback <$> go inner
        _ ->
          pure payload

    goCodeArg arg =
      case arg of
        CAObj obj -> Right (CAObj obj)
        CATm (TermDiagram inner) -> CATm . TermDiagram <$> go inner

    goBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete <$> go inner
        BAMeta hole -> Right (BAMeta hole)
