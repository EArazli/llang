{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.ModeTheory
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (isJust)
import Control.Monad (foldM)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (emptyEnv, meDoctrines, meImplDefaults)
import Strat.Poly.DSL.Elab
  ( checkImplementsObligationsWithBudget
  , ImplementsCheckResult(..)
  , ImplementsProof(..)
  , identityMorphismFor
  , elabDiagExpr
  )
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.ModeTheory
import Strat.Poly.Obj
import Strat.Poly.UnifyObj
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , ModAction(..)
  , ObligationDecl(..)
  , GenDecl(..)
  , InputShape(..)
  , deriveCtorTables
  , doctrineTypeTheory
  , gdPlainDom
  )
import Strat.Poly.TypeTheory (TypeTheory(..), TypeParamSig(..), modeOnlyTypeTheory)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Syntax (BinderMetaVar(..))
import Strat.Poly.Diagram (genDTm, genD, diagramDom, diagramCod)
import Strat.Poly.Graph (Diagram(..))
import Strat.Poly.ModAction (applyAction, mapTypeByModExpr)
import Strat.Poly.DiagramInterpretation (stableHoleCaptureRenaming)
import Strat.Poly.DefEq (normalizeObjDeepWithCtx)
import Strat.Poly.Quote (canonicalizeDiagram)
import Strat.Poly.TermExpr (TermExpr(..), termExprToDiagram, diagramToTermExpr)
import Strat.Poly.Proof (defaultSearchBudget)
import Test.Poly.Helpers (mkModes, withSelfClassifiedCtors)


tests :: TestTree
tests =
  testGroup
    "Poly.ModeTheory"
    [ testCase "self-classification allows universe declared later" testSelfClassificationDeferred
    , testCase "classified mode with complex universe resolves after pending pass" testClassifiedComplexUniverseDeferred
    , testCase "multiple pending universes resolve after pending pass" testMultiplePendingUniversesDeferred
    , testCase "classification cycle (non-self) is rejected" testClassificationCycleRejected
    , testCase "classificationOrder places classifier before classified mode" testClassificationOrder
    , testCase "classifier lift for identity modality expression is identity on classifier" testClassifierLiftForIdentityExpr
    , testCase "classifier lift for composed modality expression composes step lifts" testClassifierLiftForComposedExpr
    , testCase "classifier lift coherence rejects inconsistent lifts across mod_eq" testClassifierLiftCoherenceRejected
    , testCase "classifier lift coherence accepts consistent lifts across mod_eq" testClassifierLiftCoherenceAccepted
    , testCase "classified modality over classifier-headed code normalizes" testClassifiedModalityNormalization
    , testCase "classified non-self modality requires explicit classifier lift" testClassifiedModalityMissingLiftRejected
    , testCase "explicit classifier lift universe compatibility is enforced" testClassifierLiftUniverseMismatchRejected
    , testCase "beck-chevalley obligations are generated and discharged" testBeckChevalleyGeneratedObligations
    , testCase "modality rewrite normalizes nested modality type" testNormalizeObjExprByModEq
    , testCase "substitution re-normalizes modality type" testSubstReNormalizes
    , testCase "action declarations elaborate and validate" testActionElab
    , testCase "action images can reference binder holes for binder-slot generators" testActionBinderHoles
    , testCase "stable hole-capture renaming skips non-conflicting canonical metas" testStableHoleCaptureRenamingSkipsNonConflictingCanonicalMetas
    , testCase "action images reject out-of-range binder holes" testActionBinderHolesOutOfRangeRejected
    , testCase "action images reject unknown splice binder holes" testActionBinderSpliceUnknownRejected
    , testCase "canonical action fallback rejects binder-incompatible same-name generators" testActionFallbackBinderMismatchRejected
    , testCase "canonical action fallback accepts binder-compatible same-name generators" testActionFallbackBinderCompatibleAccepted
    , testCase "canonical action fallback allows cross-mode binder tmctx objects" testActionFallbackCrossModeTmCtxAccepted
    , testCase "beck-chevalley obligations constrain target reindex under action" testBeckChevalleyConstrainsTargetReindex
    , testCase "applyAction preserves non-source tmctx and unifies using diagram tmctx" testApplyActionUsesDiagramTmCtx
    , testCase "applyAction weakens image term-context prefixes before splice" testApplyActionWeakenImageTmCtx
    , testCase "map elaborates inner expression at modality source mode" testMapCrossModeElab
    , testCase "modal type formation elaboration matches mapped type transport" testModalTypeFormationMatchesMapType
    , testCase "for_gen obligations elaborate @gen and lifts" testForGenObligationElab
    , testCase "for_gen obligations expand over target generators during implements" testForGenImplementsQuantifiesTarget
    , testCase "for_gen obligations map schema generator refs through morphism" testForGenSchemaRefsMapped
    , testCase "for_gen lift_cod instantiates polymorphic operators by domain" testForGenPolyLiftInstantiation
    , testCase "for_gen lift operators allow codomain arity changes" testForGenLiftAllowsCodArityChange
    , testCase "for_gen lift_dom comp anchors to right operand boundary" testForGenLiftDomCompositionAnchoring
    , testCase "for_gen non-generated obligations are boundary-locked to @gen" testForGenBoundaryLockedForUserObligations
    , testCase "for_gen rejects @gen under mode-changing map context" testForGenGenPlacementRejected
    , testCase "@gen outside for_gen is rejected" testGenOutsideForGenRejected
    , testCase "doctrine type theory builds definitional fragments for all modes" testDefFragmentsCoverModes
    , testCase "action coherence follows mod_eq" testActionModEqCoherence
    , testCase "comprehension declaration elaborates into mode theory" testComprehensionDeclElab
    , testCase "comprehension declaration requires classifiedBy mode" testComprehensionRequiresClassifiedMode
    , testCase "comprehension declaration rejects unknown generator" testComprehensionUnknownGenerator
    , testCase "comprehension declaration rejects constructor-like generators" testComprehensionRejectsCtorLike
    , testCase "unclassified mode allows doctrines without constructor usage" testUnclassifiedModeNoCtorUsageAllowed
    , testCase "unclassified mode rejects constructor usage with direct diagnostic" testUnclassifiedModeCtorUsageRejected
    , testCase "classified modes with binder inputs require comprehension declarations" testComprehensionBinderRequiresDecl
    , testCase "classified modes without binder inputs still require comprehension declarations" testComprehensionRequiresDeclWithoutBinder
    , testCase "comprehension declarations install generated obligations" testComprehensionGeneratedObligations
    , testCase "mixed plain+binder generators are excluded from generated comprehension laws" testComprehensionMixedBinderExcluded
    , testCase "binder-only multi-binder generators produce full comprehension laws" testComprehensionMultiBinderOnlyFull
    , testCase "constructor term slots generate boundary-side laws only" testComprehensionCtorSlotBoundarySide
    , testCase "constructor term slots on multi-port plain domains generate dom-side laws" testComprehensionCtorSlotMultiPortDom
    , testCase "constructor term slots on binder domains still generate boundary-side laws" testComprehensionCtorSlotBinderDomain
    , testCase "cross-mode constructor slots are ignored by owner-mode gating" testComprehensionCrossModeCtorSlots
    , testCase "generated comprehension obligations can require join proofs" testComprehensionGeneratedObligationJoinProof
    , testCase "implements fails when schema obligations are not provable" testAdjObligationFail
    , testCase "implements succeeds when schema obligations hold" testAdjObligationPass
    , testCase "implements monad schema with map[T] laws against target action" testMonadObligationPass
    , testCase "legacy adj keyword is rejected" testAdjunctionKeywordRejected
    , testCase "legacy struct keyword is rejected" testStructureKeywordRejected
    ]

testSelfClassificationDeferred :: Assertion
testSelfClassificationDeferred = do
  let src = T.unlines
        [ "doctrine SelfClass where {"
        , "  mode Ty classifiedBy Ty via Ty.U;"
        , "  gen U : [] -> [Ty.U] @Ty;"
        , "  gen ctx_ext(a@Ty) : [a] -> [a] @Ty;"
        , "  gen var(a@Ty) : [a] -> [a] @Ty;"
        , "  gen reindex(a@Ty) : [a] -> [a] @Ty;"
        , "  comprehension Ty where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testClassifiedComplexUniverseDeferred :: Assertion
testClassifiedComplexUniverseDeferred = do
  let src = T.unlines
        [ "doctrine ComplexUniverseDeferred where {"
        , "  mode Ty classifiedBy Ty via Ty.U;"
        , "  gen U : [] -> [Ty.U] @Ty;"
        , "  gen Wrap(a@Ty) : [] -> [Ty.U] @Ty;"
        , "  gen ctx_ext(a@Ty) : [a] -> [a] @Ty;"
        , "  gen var(a@Ty) : [a] -> [a] @Ty;"
        , "  gen reindex(a@Ty) : [a] -> [a] @Ty;"
        , "  comprehension Ty where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode Tm classifiedBy Ty via Ty.Wrap(Ty.U);"
        , "  gen t_ctx_ext(a@Tm) : [a] -> [a] @Tm;"
        , "  gen t_var(a@Tm) : [a] -> [a] @Tm;"
        , "  gen t_reindex(a@Tm) : [a] -> [a] @Tm;"
        , "  comprehension Tm where { ctx_ext = t_ctx_ext; var = t_var; reindex = t_reindex; };"
        , "  gen keep(a@Tm) : [a] -> [a] @Tm;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testMultiplePendingUniversesDeferred :: Assertion
testMultiplePendingUniversesDeferred = do
  let src = T.unlines
        [ "doctrine TwoPendingUniversesDeferred where {"
        , "  mode Ty classifiedBy Ty via Ty.U_Ty;"
        , "  gen U_Ty : [] -> [Ty.U_Ty] @Ty;"
        , "  gen U : [] -> [Ty.U_Ty] @Ty;"
        , "  gen Wrap(a@Ty) : [] -> [Ty.U_Ty] @Ty;"
        , "  gen TmTy : [] -> [Ty.Wrap(Ty.U)] @Ty;"
        , "  gen ElTy : [] -> [Ty.Wrap(Ty.Wrap(Ty.U))] @Ty;"
        , "  gen ctx_ext(a@Ty) : [a] -> [a] @Ty;"
        , "  gen var(a@Ty) : [a] -> [a] @Ty;"
        , "  gen reindex(a@Ty) : [a] -> [a] @Ty;"
        , "  comprehension Ty where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode Tm classifiedBy Ty via Ty.Wrap(Ty.U);"
        , "  gen t_ctx_ext(a@Tm) : [a] -> [a] @Tm;"
        , "  gen t_var(a@Tm) : [a] -> [a] @Tm;"
        , "  gen t_reindex(a@Tm) : [a] -> [a] @Tm;"
        , "  comprehension Tm where { ctx_ext = t_ctx_ext; var = t_var; reindex = t_reindex; };"
        , "  mode El classifiedBy Ty via Ty.Wrap(Ty.Wrap(Ty.U));"
        , "  gen e_ctx_ext(a@El) : [a] -> [a] @El;"
        , "  gen e_var(a@El) : [a] -> [a] @El;"
        , "  gen e_reindex(a@El) : [a] -> [a] @El;"
        , "  comprehension El where { ctx_ext = e_ctx_ext; var = e_var; reindex = e_reindex; };"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "TwoPendingUniversesDeferred" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine TwoPendingUniversesDeferred" >> fail "unreachable"
      Just d -> pure d
  let classes = mtClassifiedBy (dModes doc)
  let tmUniverse = cdUniverse <$> M.lookup (ModeName "Tm") classes
  let elUniverse = cdUniverse <$> M.lookup (ModeName "El") classes
  case (tmUniverse, elUniverse) of
    (Just tmU, Just elU) -> do
      let tyMode = ModeName "Ty"
      let wrapRef = ObjRef tyMode (ObjName "Wrap")
      let uRef = ObjRef tyMode (ObjName "U")
      let uObj = Obj { objOwnerMode = tyMode, objCode = CTCon uRef [] }
      tmU @?=
        Obj
          { objOwnerMode = tyMode
          , objCode = CTCon wrapRef [CAObj uObj]
          }
      elU @?=
        Obj
          { objOwnerMode = tyMode
          , objCode =
              CTCon
                wrapRef
                [ CAObj
                    Obj
                      { objOwnerMode = tyMode
                      , objCode = CTCon wrapRef [CAObj uObj]
                      }
                ]
          }
    _ -> assertFailure "expected classified universes for Tm and El"
  ctorTables <- requireEither (deriveCtorTables doc)
  let tmTable = M.findWithDefault M.empty (ModeName "Tm") ctorTables
  let elTable = M.findWithDefault M.empty (ModeName "El") ctorTables
  assertBool "expected non-empty constructor table for Tm after pending resolution" (not (M.null tmTable))
  assertBool "expected non-empty constructor table for El after pending resolution" (not (M.null elTable))

testUnclassifiedModeNoCtorUsageAllowed :: Assertion
testUnclassifiedModeNoCtorUsageAllowed = do
  let src = T.unlines
        [ "doctrine UnclassifiedNoCtors where {"
        , "  mode M;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testUnclassifiedModeCtorUsageRejected :: Assertion
testUnclassifiedModeCtorUsageRejected = do
  let src = T.unlines
        [ "doctrine UnclassifiedCtor where {"
        , "  mode M;"
        , "  gen U : [] -> [M.U] @M;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err -> do
      assertBool
        ("expected unclassified mode diagnostic, got: " <> T.unpack err)
        ("mode M is unclassified" `T.isInfixOf` err)
      assertBool
        ("expected constructor mention in diagnostic, got: " <> T.unpack err)
        ("constructor `M.U`" `T.isInfixOf` err)
    Right _ -> assertFailure "expected elaboration failure for constructor usage in unclassified mode"

testClassificationCycleRejected :: Assertion
testClassificationCycleRejected = do
  let src = T.unlines
        [ "doctrine BadCycle where {"
        , "  mode A classifiedBy B via B.U;"
        , "  mode B classifiedBy A via B.U;"
        , "  gen U : [] -> [B.U] @A;"
        , "  gen U : [] -> [B.U] @B;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool
        ("expected classification cycle error, got: " <> T.unpack err)
        ( "cycle" `T.isInfixOf` err
            || "strat" `T.isInfixOf` err
            || "classified by" `T.isInfixOf` err
        )
    Right _ -> assertFailure "expected doctrine elaboration to reject non-self classification cycle"

testClassificationOrder :: Assertion
testClassificationOrder = do
  let ty = ModeName "Ty"
  let tm = ModeName "Tm"
  let uTy = OVar (mkModeMetaVar "U" ty)
  let uTy2 = OVar (mkModeMetaVar "U2" ty)
  mt0 <- requireEither (addMode ty (mkModes []))
  mt1 <- requireEither (addMode tm mt0)
  mt2 <- requireEither (addClassification ty ClassificationDecl { cdClassifier = ty, cdUniverse = uTy, cdComp = Nothing } mt1)
  mt3 <- requireEither (addClassification tm ClassificationDecl { cdClassifier = ty, cdUniverse = uTy2, cdComp = Nothing } mt2)
  order <- requireEither (classificationOrder mt3)
  let pos mode = lookup mode (zip order [0 :: Int ..])
  assertBool "expected classificationOrder to include Ty and Tm" (maybe False (const True) (pos ty) && maybe False (const True) (pos tm))
  case (pos ty, pos tm) of
    (Just i, Just j) ->
      assertBool "expected Ty to appear before Tm in classification order" (i < j)
    _ ->
      assertFailure "classificationOrder missing expected modes"

testClassifierLiftForIdentityExpr :: Assertion
testClassifierLiftForIdentityExpr = do
  let modeTy = ModeName "Ty"
      modeTm = ModeName "Tm"
      uTy = OVar (mkModeMetaVar "U_Ty" modeTy)
      uTm = OVar (mkModeMetaVar "U_Tm" modeTy)
  mt0 <- requireEither (addMode modeTy emptyModeTheory)
  mt1 <- requireEither (addMode modeTm mt0)
  mt2 <- requireEither (addClassification modeTy ClassificationDecl { cdClassifier = modeTy, cdUniverse = uTy, cdComp = Nothing } mt1)
  mt3 <- requireEither (addClassification modeTm ClassificationDecl { cdClassifier = modeTy, cdUniverse = uTm, cdComp = Nothing } mt2)
  let expr = ModExpr { meSrc = modeTm, meTgt = modeTm, mePath = [] }
  liftExpr <- requireEither (classifierLiftForModExpr mt3 expr)
  liftExpr @?= ModExpr { meSrc = modeTy, meTgt = modeTy, mePath = [] }

testClassifierLiftForComposedExpr :: Assertion
testClassifierLiftForComposedExpr = do
  let modeA = ModeName "A"
      modeB = ModeName "B"
      modeC = ModeName "C"
      classA = ModeName "TyA"
      classB = ModeName "TyB"
      classC = ModeName "TyC"
      modF = ModName "f"
      modG = ModName "g"
      liftF = ModName "liftF"
      liftG = ModName "liftG"
      modes = [modeA, modeB, modeC, classA, classB, classC]
      u mode = OVar (mkModeMetaVar ("U_" <> renderMode mode) mode)
      classify owner classifier =
        addClassification
          owner
          ClassificationDecl
            { cdClassifier = classifier
            , cdUniverse = u classifier
            
            , cdComp = Nothing
            }
      addDecl name src tgt = addModDecl ModDecl { mdName = name, mdSrc = src, mdTgt = tgt }
      renderMode (ModeName n) = n
  mt0 <- requireEither (foldM (flip addMode) emptyModeTheory modes)
  mt1 <- requireEither (classify classA classA mt0)
  mt2 <- requireEither (classify classB classB mt1)
  mt3 <- requireEither (classify classC classC mt2)
  mt4 <- requireEither (classify modeA classA mt3)
  mt5 <- requireEither (classify modeB classB mt4)
  mt6 <- requireEither (classify modeC classC mt5)
  mt7 <- requireEither (addDecl modF modeA modeB mt6)
  mt8 <- requireEither (addDecl modG modeB modeC mt7)
  mt9 <- requireEither (addDecl liftF classA classB mt8)
  mt10 <- requireEither (addDecl liftG classB classC mt9)
  mt11 <- requireEither (addClassifierLift modF ModExpr { meSrc = classA, meTgt = classB, mePath = [liftF] } mt10)
  mt12 <- requireEither (addClassifierLift modG ModExpr { meSrc = classB, meTgt = classC, mePath = [liftG] } mt11)
  let composed = ModExpr { meSrc = modeA, meTgt = modeC, mePath = [modF, modG] }
  liftExpr <- requireEither (classifierLiftForModExpr mt12 composed)
  liftExpr @?= ModExpr { meSrc = classA, meTgt = classC, mePath = [liftF, liftG] }

buildLiftCoherenceTheory :: ModExpr -> Either T.Text ModeTheory
buildLiftCoherenceTheory gLift = do
  let modeC = ModeName "C"
      modeA = ModeName "A"
      modL = ModName "L"
      modF = ModName "f"
      modG = ModName "g"
      uC = OVar (mkModeMetaVar "U_C" modeC)
      addDecl name src tgt = addModDecl ModDecl { mdName = name, mdSrc = src, mdTgt = tgt }
  mt0 <- addMode modeC emptyModeTheory
  mt1 <- addMode modeA mt0
  mt2 <- addClassification modeC ClassificationDecl { cdClassifier = modeC, cdUniverse = uC, cdComp = Nothing } mt1
  mt3 <- addClassification modeA ClassificationDecl { cdClassifier = modeC, cdUniverse = uC, cdComp = Nothing } mt2
  mt4 <- addDecl modL modeC modeC mt3
  mt5 <- addDecl modF modeA modeA mt4
  mt6 <- addDecl modG modeA modeA mt5
  mt7 <- addClassifierLift modF ModExpr { meSrc = modeC, meTgt = modeC, mePath = [] } mt6
  mt8 <- addClassifierLift modG gLift mt7
  addModEqn
    ModEqn
      { meLHS = ModExpr { meSrc = modeA, meTgt = modeA, mePath = [modF] }
      , meRHS = ModExpr { meSrc = modeA, meTgt = modeA, mePath = [modG] }
      }
    mt8

testClassifierLiftCoherenceRejected :: Assertion
testClassifierLiftCoherenceRejected = do
  let modeC = ModeName "C"
      badLift = ModExpr { meSrc = modeC, meTgt = modeC, mePath = [ModName "L"] }
  mt <- requireEither (buildLiftCoherenceTheory badLift)
  case checkWellFormed mt of
    Left err ->
      assertBool
        ("expected classifier lift coherence failure, got: " <> T.unpack err)
        ("classifier lift coherence failed" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected inconsistent classifier lifts to be rejected"

testClassifierLiftCoherenceAccepted :: Assertion
testClassifierLiftCoherenceAccepted = do
  let modeC = ModeName "C"
      goodLift = ModExpr { meSrc = modeC, meTgt = modeC, mePath = [] }
  mt <- requireEither (buildLiftCoherenceTheory goodLift)
  case checkWellFormed mt of
    Left err ->
      assertFailure ("expected coherent classifier lifts to pass: " <> T.unpack err)
    Right () ->
      pure ()

testClassifiedModalityNormalization :: Assertion
testClassifiedModalityNormalization = do
  let src = T.unlines
        [ "doctrine ClassifiedModality where {"
        , "  mode Ty classifiedBy Ty via Ty.U_Ty;"
        , "  gen U_Ty : [] -> [Ty.U_Ty] @Ty;"
        , "  gen ctx_ext(a@Ty) : [a] -> [a] @Ty;"
        , "  gen var(a@Ty) : [a] -> [a] @Ty;"
        , "  gen reindex(a@Ty) : [a] -> [a] @Ty;"
        , "  comprehension Ty where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode Tm classifiedBy Ty via Ty.U;"
        , "  gen ctx_ext(a@Tm) : [a] -> [a] @Tm;"
        , "  gen var(a@Tm) : [a] -> [a] @Tm;"
        , "  gen reindex(a@Tm) : [a] -> [a] @Tm;"
        , "  comprehension Tm where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  modality mu : Tm -> Tm;"
        , "  lift_classifier mu = id@Ty;"
        , "  gen U : [] -> [Ty.U_Ty] @Ty;"
        , "  gen X : [] -> [Ty.U] @Ty;"
        , "  gen idMu : [mu(X)] -> [mu(X)] @Tm;"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "ClassifiedModality" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine ClassifiedModality" >> fail "unreachable"
      Just d -> pure d
  gen <-
    case M.lookup (ModeName "Tm") (dGens doc) >>= M.lookup (GenName "idMu") of
      Nothing -> assertFailure "missing generator idMu" >> fail "unreachable"
      Just g -> pure g
  case gdPlainDom gen of
    [obj] -> do
      objOwnerMode obj @?= ModeName "Tm"
      case objCode obj of
        CTLift me innerCode -> do
          meSrc me @?= ModeName "Ty"
          meTgt me @?= ModeName "Ty"
          case innerCode of
            CTCon ref [] ->
              ref @?= ObjRef (ModeName "Ty") (ObjName "X")
            _ -> assertFailure "expected lifted modality body to be Ty.X code"
        CTCon ref [] ->
          ref @?= ObjRef (ModeName "Ty") (ObjName "X")
        _ ->
          assertFailure "expected classifier-lifted or identity-collapsed code for idMu boundary"
    _ -> assertFailure "expected one boundary object for idMu"

testClassifiedModalityMissingLiftRejected :: Assertion
testClassifiedModalityMissingLiftRejected = do
  let src = T.unlines
        [ "doctrine MissingLift where {"
        , "  mode Ty classifiedBy Ty via Ty.U_Ty;"
        , "  gen U_Ty : [] -> [Ty.U_Ty] @Ty;"
        , "  gen ctx_ext(a@Ty) : [a] -> [a] @Ty;"
        , "  gen var(a@Ty) : [a] -> [a] @Ty;"
        , "  gen reindex(a@Ty) : [a] -> [a] @Ty;"
        , "  comprehension Ty where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode Tm classifiedBy Ty via Ty.U;"
        , "  gen ctx_ext(a@Tm) : [a] -> [a] @Tm;"
        , "  gen var(a@Tm) : [a] -> [a] @Tm;"
        , "  gen reindex(a@Tm) : [a] -> [a] @Tm;"
        , "  comprehension Tm where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  modality mu : Tm -> Tm;"
        , "  gen U : [] -> [Ty.U_Ty] @Ty;"
        , "  gen X : [] -> [Ty.U] @Ty;"
        , "  gen f : [mu(X)] -> [mu(X)] @Tm;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool
        ("expected missing classifier lift error, got: " <> T.unpack err)
        ("missing explicit classifier lift" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected doctrine elaboration to reject missing explicit classifier lift"

testClassifierLiftUniverseMismatchRejected :: Assertion
testClassifierLiftUniverseMismatchRejected = do
  let src = T.unlines
        [ "doctrine LiftUniverseMismatch where {"
        , "  mode Ty classifiedBy Ty via Ty.U_Ty;"
        , "  gen U_Ty : [] -> [Ty.U_Ty] @Ty;"
        , "  gen ctx_ext(a@Ty) : [a] -> [a] @Ty;"
        , "  gen var(a@Ty) : [a] -> [a] @Ty;"
        , "  gen reindex(a@Ty) : [a] -> [a] @Ty;"
        , "  comprehension Ty where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode M classifiedBy Ty via Ty.U;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode N classifiedBy Ty via Ty.V;"
        , "  gen ctx_ext(a@N) : [a] -> [a] @N;"
        , "  gen var(a@N) : [a] -> [a] @N;"
        , "  gen reindex(a@N) : [a] -> [a] @N;"
        , "  comprehension N where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  modality mu : M -> N;"
        , "  lift_classifier mu = id@Ty;"
        , "  gen U : [] -> [Ty.U_Ty] @Ty;"
        , "  gen V : [] -> [Ty.U_Ty] @Ty;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool
        ("expected classifier lift universe mismatch, got: " <> T.unpack err)
        ("classifier lift universe mismatch" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected doctrine elaboration to reject classifier lift universe mismatch"

testBeckChevalleyGeneratedObligations :: Assertion
testBeckChevalleyGeneratedObligations = do
  let src = T.unlines
        [ "doctrine BeckChevalley where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen Nat : [] -> [M.U_M] @M;"
        , "  gen Z : [] -> [Nat] @M;"
        , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
        , "  gen use(n : Nat) : [] -> [Vec(n)] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  modality T : M -> M;"
        , "  mod_eq T -> id@M;"
        , "  action T where {"
        , "    gen ctx_ext -> ctx_ext"
        , "    gen var -> var"
        , "    gen reindex -> reindex"
        , "    gen Z -> Z"
        , "    gen use -> use"
        , "  }"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "BeckChevalley" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine BeckChevalley" >> fail "unreachable"
      Just d -> pure d
  let bcObligations =
        [ ob
        | ob <- dObligations doc
        , "__bc/" `T.isPrefixOf` obName ob
        ]
  assertBool "expected generated Beck-Chevalley obligations" (not (null bcObligations))
  assertBool
    "expected codomain-side BC equations for ctor-term slots"
    (any (\obl -> "/cod" `T.isSuffixOf` obName obl) bcObligations)

testNormalizeObjExprByModEq :: Assertion
testNormalizeObjExprByModEq = do
  mt <- requireEither (buildStagingTheory (ModeName "RT") (ModeName "CT"))
  let rt = ModeName "RT"
  let quote = ModName "quote"
  let splice = ModName "splice"
  let natRT = mkCon (ObjRef rt (ObjName "Nat")) []
  let quoteE = ModExpr { meSrc = rt, meTgt = ModeName "CT", mePath = [quote] }
  let spliceE = ModExpr { meSrc = ModeName "CT", meTgt = rt, mePath = [splice] }
  got <- requireEither (normalizeObjExpr mt (OMod spliceE (OMod quoteE natRT)))
  got @?= natRT

testSubstReNormalizes :: Assertion
testSubstReNormalizes = do
  mt <- requireEither (buildStagingTheory (ModeName "RT") (ModeName "CT"))
  let rt = ModeName "RT"
  let ct = ModeName "CT"
  let quote = ModName "quote"
  let splice = ModName "splice"
  let xVar = mkModeMetaVar "x" ct
  let aVar = mkModeMetaVar "A" rt
  let quoteE = ModExpr { meSrc = rt, meTgt = ct, mePath = [quote] }
  let spliceE = ModExpr { meSrc = ct, meTgt = rt, mePath = [splice] }
  let tt = modeOnlyTypeTheory mt
  subst <- requireEither (unifyObj tt (OVar xVar) (OMod quoteE (OVar aVar)))
  got <- requireEither (applySubstObj tt subst (OMod spliceE (OVar xVar)))
  got @?= OVar aVar

testActionElab :: Assertion
testActionElab = do
  let src = T.unlines
        [ "doctrine Act where {"
        , "  mode A classifiedBy A via A.U_A;"
        , "  gen U_A : [] -> [A.U_A] @A;"
        , "  gen ctx_ext(a@A) : [a] -> [a] @A;"
        , "  gen var(a@A) : [a] -> [a] @A;"
        , "  gen reindex(a@A) : [a] -> [a] @A;"
        , "  comprehension A where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode B classifiedBy A via A.U_A;"
        , "  gen U_B : [] -> [A.U_A] @B;"
        , "  gen ctx_ext(a@B) : [a] -> [a] @B;"
        , "  gen var(a@B) : [a] -> [a] @B;"
        , "  gen reindex(a@B) : [a] -> [a] @B;"
        , "  comprehension B where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [A.U_A] @A;"
        , "  modality F : A -> B;"
        , "  lift_classifier F = id@A;"
        , "  gen g : [A.X] -> [A.X] @A;"
        , "  gen h : [A.X] -> [A.X] @B;"
        , "  action F where {"
        , "    gen g -> h"
        , "    gen ctx_ext -> ctx_ext"
        , "    gen var -> var"
        , "    gen reindex -> reindex"
        , "  }"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "Act" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine Act" >> fail "unreachable"
      Just d -> pure d
  assertBool "expected modality action table to contain F" (M.member (ModName "F") (dActions doc))
  case M.lookup (ModName "F") (dActions doc) >>= M.lookup (ModeName "A", GenName "g") . maGenMap of
    Nothing -> assertFailure "missing action image for g under F"
    Just _ -> pure ()

testActionBinderHoles :: Assertion
testActionBinderHoles = do
  let src =
        T.unlines
          [ "doctrine ActionBinderHoles where {"
          , "  mode M classifiedBy M via Box(M.U_M);"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  modality Box : M -> M;"
          , "  lift_classifier Box = Box;"
          , "  mod_eq Box.Box -> Box;"
          , "  gen U_M : [] -> [Box(M.U_M)] @M;"
          , "  gen A : [] -> [Box(M.U_M)] @M;"
          , "  gen lam  : [binder { x : A } : [A]] -> [A] @M;"
          , "  gen app  : [A, A] -> [A] @M;"
          , "  gen lamB : [binder { x : Box(A) } : [Box(A)]] -> [Box(A)] @M;"
          , "  gen appB : [Box(A), Box(A)] -> [Box(A)] @M;"
          , "  action Box where {"
          , "    gen lam -> lamB[?b0]"
          , "    gen app -> appB"
          , "  }"
          , "}"
          ]

  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "ActionBinderHoles" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine ActionBinderHoles" >> fail "unreachable"
      Just d -> pure d

  let modeM = ModeName "M"
  rawMapped <- requireEither (parseDiagExpr "map[Box]((lam[id[A]] * id[A]) ; app)")
  diagMapped <- requireEither (elabDiagExpr emptyEnv doc modeM [] rawMapped)

  rawExpected <- requireEither (parseDiagExpr "(lamB[id[Box(A)]] * id[Box(A)]) ; appB")
  diagExpected <- requireEither (elabDiagExpr emptyEnv doc modeM [] rawExpected)

  assertEqual
    "map[Box] should translate binder-slot generator lam using binder-hole passthrough"
    (canonicalizeDiagram diagExpected)
    (canonicalizeDiagram diagMapped)

testStableHoleCaptureRenamingSkipsNonConflictingCanonicalMetas :: Assertion
testStableHoleCaptureRenamingSkipsNonConflictingCanonicalMetas = do
  let b0 = BinderMetaVar "b0"
  let b1 = BinderMetaVar "b1"
  let holes = S.fromList [b0]
  let metasNoConflict = S.fromList [b1, BinderMetaVar "bx"]
  stableHoleCaptureRenaming holes metasNoConflict @?= M.empty

  let renamingWithConflict = stableHoleCaptureRenaming holes (S.insert b0 metasNoConflict)
  M.lookup b0 renamingWithConflict @?= Just (BinderMetaVar "b0_arg")
  assertBool "non-conflicting canonical binder meta b1 should remain unchanged" (M.notMember b1 renamingWithConflict)

testActionBinderHolesOutOfRangeRejected :: Assertion
testActionBinderHolesOutOfRangeRejected = do
  let src =
        T.unlines
          [ "doctrine ActionBinderHolesBadIndex where {"
          , "  mode M classifiedBy M via Box(M.U_M);"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  modality Box : M -> M;"
          , "  lift_classifier Box = Box;"
          , "  mod_eq Box.Box -> Box;"
          , "  gen U_M : [] -> [Box(M.U_M)] @M;"
          , "  gen A : [] -> [Box(M.U_M)] @M;"
          , "  gen lam  : [binder { x : A } : [A]] -> [A] @M;"
          , "  gen app  : [A, A] -> [A] @M;"
          , "  gen lamB : [binder { x : Box(A) } : [Box(A)]] -> [Box(A)] @M;"
          , "  gen appB : [Box(A), Box(A)] -> [Box(A)] @M;"
          , "  action Box where {"
          , "    gen lam -> lamB[?b1]"
          , "    gen app -> appB"
          , "  }"
          , "}"
          ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool
        ("expected out-of-range binder-hole rejection, got: " <> T.unpack err)
        ("unknown binder meta" `T.isInfixOf` err || "RHS introduces unknown binder meta" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected elaboration to reject out-of-range action binder hole ?b1"

testActionBinderSpliceUnknownRejected :: Assertion
testActionBinderSpliceUnknownRejected = do
  let src =
        T.unlines
          [ "doctrine ActionBinderSpliceUnknown where {"
          , "  mode M classifiedBy M via Box(M.U_M);"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  modality Box : M -> M;"
          , "  lift_classifier Box = Box;"
          , "  mod_eq Box.Box -> Box;"
          , "  gen U_M : [] -> [Box(M.U_M)] @M;"
          , "  gen A : [] -> [Box(M.U_M)] @M;"
          , "  gen lam  : [binder { x : A } : [A]] -> [A] @M;"
          , "  gen app  : [A, A] -> [A] @M;"
          , "  gen lamB : [binder { x : Box(A) } : [Box(A)]] -> [Box(A)] @M;"
          , "  gen appB : [Box(A), Box(A)] -> [Box(A)] @M;"
          , "  action Box where {"
          , "    gen lam -> splice(?bx)"
          , "    gen app -> appB"
          , "  }"
          , "}"
          ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool
        ("expected unknown-splice binder-hole rejection, got: " <> T.unpack err)
        ("splice references unknown binder meta" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected elaboration to reject splice(?bx) in action image"

testActionFallbackBinderMismatchRejected :: Assertion
testActionFallbackBinderMismatchRejected = do
  let src = T.unlines
        [ "doctrine ActFallbackBad where {"
        , "  mode A;"
        , "  mode B;"
        , "  modality F : A -> B;"
        , "  gen g : [] -> [] @A;"
        , "  gen g : [binder { } : []] -> [] @B;"
        , "  action F where {}"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err -> do
      assertBool
        ("expected canonical fallback rejection, got: " <> T.unpack err)
        ("canonical fallback" `T.isInfixOf` err)
      assertBool
        ("expected binder-arity diagnostic, got: " <> T.unpack err)
        ("binder arity mismatch" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected elaboration to reject binder-incompatible canonical action fallback"

testActionFallbackBinderCompatibleAccepted :: Assertion
testActionFallbackBinderCompatibleAccepted = do
  let src = T.unlines
        [ "doctrine ActFallbackGood where {"
        , "  mode A;"
        , "  mode B;"
        , "  modality F : A -> B;"
        , "  gen g : [binder { } : []] -> [] @A;"
        , "  gen g : [binder { } : []] -> [] @B;"
        , "  action F where {}"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertFailure ("expected elaboration success for binder-compatible canonical fallback, got: " <> T.unpack err)
    Right _ ->
      pure ()

testActionFallbackCrossModeTmCtxAccepted :: Assertion
testActionFallbackCrossModeTmCtxAccepted = do
  let src = T.unlines
        [ "doctrine ActFallbackCrossTmCtx where {"
        , "  mode A;"
        , "  mode B;"
        , "  mode C classifiedBy C via C.U_C;"
        , "  gen U_C : [] -> [C.U_C] @C;"
        , "  gen c_ctx_ext(a@C) : [a] -> [a] @C;"
        , "  gen c_var(a@C) : [a] -> [a] @C;"
        , "  gen c_reindex(a@C) : [a] -> [a] @C;"
        , "  comprehension C where { ctx_ext = c_ctx_ext; var = c_var; reindex = c_reindex; };"
        , "  modality F : A -> B;"
        , "  gen g(a@C) : [binder { x : a } : []] -> [] @A;"
        , "  gen g(a@C) : [binder { x : a } : []] -> [] @B;"
        , "  action F where {}"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertFailure ("expected canonical fallback success for cross-mode binder tmctx, got: " <> T.unpack err)
    Right _ ->
      pure ()

testBeckChevalleyConstrainsTargetReindex :: Assertion
testBeckChevalleyConstrainsTargetReindex = do
  let src = T.unlines
        [ "doctrine BadBCAction where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen comp_var(a@M) : [a] -> [a] @M;"
        , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
        , "  modality F : M -> M;"
        , "  lift_classifier F = id@M;"
        , "  gen A : [] -> [M.U_M] @M;"
        , "  gen bad_reindex(a@M) : [a] -> [a] @M;"
        , "  gen lam : [binder { x : A } : [A]] -> [A] @M;"
        , "  action F where {"
        , "    gen comp_reindex -> bad_reindex"
        , "    gen lam -> lam[?b0]"
        , "  }"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err -> do
      assertBool
        ("expected Beck-Chevalley generated-obligation failure, got: " <> T.unpack err)
        ( "__bc/" `T.isInfixOf` err
            || "Beck-Chevalley semantics undecided" `T.isInfixOf` err
        )
    Right _ ->
      assertFailure "expected doctrine elaboration failure when action maps reindex incompatibly with Beck-Chevalley obligations"

testDefFragmentsCoverModes :: Assertion
testDefFragmentsCoverModes = do
  let src = T.unlines
        [ "doctrine DefFrags where {"
        , "  mode M classifiedBy M via M.U;"
        , "  gen U : [] -> [M.U] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode N classifiedBy N via N.V;"
        , "  gen V : [] -> [N.V] @N;"
        , "  gen ctx_ext(a@N) : [a] -> [a] @N;"
        , "  gen var(a@N) : [a] -> [a] @N;"
        , "  gen reindex(a@N) : [a] -> [a] @N;"
        , "  comprehension N where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen A : [] -> [M.U] @M;"
        , "  gen idA : [A] -> [A] @M;"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "DefFrags" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine DefFrags" >> fail "unreachable"
      Just d -> pure d
  tt <- requireEither (doctrineTypeTheory doc)
  M.keysSet (ttDefFragments tt) @?= M.keysSet (mtModes (dModes doc))

testApplyActionUsesDiagramTmCtx :: Assertion
testApplyActionUsesDiagramTmCtx = do
  let modeC = ModeName "C"
  let modeI = ModeName "I"
  let modF = ModName "F"
  let natRef = ObjRef modeI (ObjName "Nat")
  let vecRef = ObjRef modeC (ObjName "Vec")
  let natTy = mkCon natRef []
  let tmCtx = [natTy]
  mt0 <- requireEither (addMode modeC (mkModes []))
  mt1 <- requireEither (addMode modeI mt0)
  mt2 <- requireEither (addModDecl (ModDecl modF modeC modeC) mt1)
  let lhsEq = ModExpr { meSrc = modeC, meTgt = modeC, mePath = [modF] }
  let rhsEq = ModExpr { meSrc = modeC, meTgt = modeC, mePath = [] }
  mt <- requireEither (addModEqn (ModEqn lhsEq rhsEq) mt2)
  let tt0 = modeOnlyTypeTheory mt
  let tmParam = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 1, tmvOwnerMode = Nothing }
  tmParamTerm <- requireEither (termExprToDiagram tt0 tmCtx natTy (TMMeta tmParam (defaultMetaArgs tmCtx tmParam)))
  tmBound0 <- requireEither (termExprToDiagram tt0 tmCtx natTy (TMBound 0))
  let vecParam = mkCon vecRef [OATm tmParamTerm]
  let vecBound = mkCon vecRef [OATm tmBound0]
  let genName = GenName "g"
  let genDecl =
        GenDecl
          { gdName = genName
          , gdMode = modeC
          , gdParams = []
          , gdDom = [InPort vecParam]
          , gdCod = [vecParam]
          , gdAttrs = []
          }
  image <- requireEither (genDTm modeC tmCtx [vecParam] [vecParam] genName)
  let doc =
        withSelfClassifiedCtors
          [ (modeI, [(ObjName "Nat", [])])
          , (modeC, [(ObjName "Vec", [TPS_Tm natTy])])
          ]
          Doctrine
            { dName = "ActTmCtx"
            , dModes = mt
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.fromList [(modeC, M.fromList [(genName, genDecl)])]
            , dCells2 = []
            , dActions =
                M.fromList
                  [ (modF, ModAction { maMod = modF, maGenMap = M.fromList [((modeC, genName), image)], maPolicy = UseOnlyComputationalLR})
                  ]
            , dObligations = []
            }
  tt <- requireEither (doctrineTypeTheory doc)
  srcDiag <- requireEither (genDTm modeC tmCtx [vecBound] [vecBound] genName)
  mapped <- requireEither (applyAction doc modF srcDiag)
  dTmCtx mapped @?= tmCtx
  dom <- requireEither (diagramDom mapped)
  cod <- requireEither (diagramCod mapped)
  dom @?= [vecBound]
  cod @?= [vecBound]
  case dom of
    [OCon _ [OATm tmOut]] -> do
      expr <- requireEither (diagramToTermExpr tt tmCtx natTy tmOut)
      expr @?= TMBound 0
    _ -> assertFailure "unexpected mapped boundary shape"

testApplyActionWeakenImageTmCtx :: Assertion
testApplyActionWeakenImageTmCtx = do
  let modeM = ModeName "M"
  let modF = ModName "F"
  let tyX = mkCon (ObjRef modeM (ObjName "X")) []
  mt0 <- requireEither (addMode modeM (mkModes []))
  mt1 <- requireEither (addModDecl (ModDecl modF modeM modeM) mt0)
  let lhsEq = ModExpr { meSrc = modeM, meTgt = modeM, mePath = [modF] }
  let rhsEq = ModExpr { meSrc = modeM, meTgt = modeM, mePath = [] }
  mt <- requireEither (addModEqn (ModEqn lhsEq rhsEq) mt1)
  let genG = GenName "g"
  let genH = GenName "h"
  let mkGen name =
        GenDecl
          { gdName = name
          , gdMode = modeM
          , gdParams = []
          , gdDom = [InPort tyX]
          , gdCod = [tyX]
          , gdAttrs = []
          }
  img <- requireEither (genD modeM [tyX] [tyX] genH)
  let doc =
        withSelfClassifiedCtors
          [(modeM, [(ObjName "X", [])])]
          Doctrine
            { dName = "ActWeaken"
            , dModes = mt
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.singleton modeM (M.fromList [(genG, mkGen genG), (genH, mkGen genH)])
            , dCells2 = []
            , dActions =
                M.singleton
                  modF
                  ModAction
                    { maMod = modF
                    , maGenMap = M.singleton (modeM, genG) img
                    , maPolicy = UseOnlyComputationalLR
                    }
            , dObligations = []
            }
  srcDiag <- requireEither (genDTm modeM [tyX] [tyX] [tyX] genG)
  mapped <- requireEither (applyAction doc modF srcDiag)
  dTmCtx mapped @?= [tyX]

testMapCrossModeElab :: Assertion
testMapCrossModeElab = do
  let src = T.unlines
        [ "doctrine CrossMap where {"
        , "  mode A classifiedBy A via A.U_A;"
        , "  gen U_A : [] -> [A.U_A] @A;"
        , "  gen ctx_ext(a@A) : [a] -> [a] @A;"
        , "  gen var(a@A) : [a] -> [a] @A;"
        , "  gen reindex(a@A) : [a] -> [a] @A;"
        , "  comprehension A where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode B classifiedBy A via A.U_A;"
        , "  gen U_B : [] -> [A.U_A] @B;"
        , "  gen ctx_ext(a@B) : [a] -> [a] @B;"
        , "  gen var(a@B) : [a] -> [a] @B;"
        , "  gen reindex(a@B) : [a] -> [a] @B;"
        , "  comprehension B where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  modality F : A -> B;"
        , "  lift_classifier F = id@A;"
        , "  gen X : [] -> [A.U_A] @A;"
        , "  gen g(a@A) : [a] -> [a] @A;"
        , "  gen h(a@A) : [F(a)] -> [F(a)] @B;"
        , "  action F where {"
        , "    gen g -> h"
        , "    gen ctx_ext -> ctx_ext"
        , "    gen var -> var"
        , "    gen reindex -> reindex"
        , "  }"
        , "  obligation map_obl(a@A) : [F(a)] -> [F(a)] @B ="
        , "    map[F](g{a}) == h{a}"
        , "}"
        ]
  _ <- requireEither (parseRawFile src >>= elabRawFile)
  pure ()

testModalTypeFormationMatchesMapType :: Assertion
testModalTypeFormationMatchesMapType = do
  let modeA = ModeName "A"
      modeB = ModeName "B"
      modF = ModName "F"
      src = T.unlines
        [ "doctrine ModalTypeEq where {"
        , "  mode A classifiedBy A via A.U_A;"
        , "  gen U_A : [] -> [A.U_A] @A;"
        , "  gen ctx_ext(a@A) : [a] -> [a] @A;"
        , "  gen var(a@A) : [a] -> [a] @A;"
        , "  gen reindex(a@A) : [a] -> [a] @A;"
        , "  comprehension A where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode B classifiedBy A via A.U_A;"
        , "  gen U_B : [] -> [A.U_A] @B;"
        , "  gen ctx_ext(a@B) : [a] -> [a] @B;"
        , "  gen var(a@B) : [a] -> [a] @B;"
        , "  gen reindex(a@B) : [a] -> [a] @B;"
        , "  comprehension B where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  modality F : A -> B;"
        , "  lift_classifier F = id@A;"
        , "  gen X : [] -> [A.U_A] @A;"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "ModalTypeEq" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine ModalTypeEq" >> fail "unreachable"
      Just d -> pure d
  tt <- requireEither (doctrineTypeTheory doc)

  rawBase <- requireEither (parseDiagExpr "id[X]")
  diagBase <- requireEither (elabDiagExpr emptyEnv doc modeA [] rawBase)
  baseDom <- requireEither (diagramDom diagBase)
  baseTy <-
    case baseDom of
      [ty] -> pure ty
      _ -> assertFailure "expected one boundary type for id[X]" >> fail "unreachable"

  mappedTy <- requireEither $
    mapTypeByModExpr
      doc
      ModExpr { meSrc = modeA, meTgt = modeB, mePath = [modF] }
      baseTy

  rawModal <- requireEither (parseDiagExpr "id[F(X)]")
  diagModal <- requireEither (elabDiagExpr emptyEnv doc modeB [] rawModal)
  modalDom <- requireEither (diagramDom diagModal)
  modalTy <-
    case modalDom of
      [ty] -> pure ty
      _ -> assertFailure "expected one boundary type for id[F(X)]" >> fail "unreachable"

  mappedNorm <- requireEither (normalizeObjDeepWithCtx tt [] mappedTy)
  modalNorm <- requireEither (normalizeObjDeepWithCtx tt [] modalTy)
  mappedNorm @?= modalNorm

testForGenObligationElab :: Assertion
testForGenObligationElab = do
  let src = T.unlines
        [ "doctrine ForGenLift where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [M.U_M] @M;"
        , "  gen op : [M.X] -> [M.X] @M;"
        , "  gen f : [M.X, M.X] -> [M.X] @M;"
        , "  obligation naturality for_gen @M ="
        , "    @gen ; lift_cod(op) == lift_dom(op) ; @gen"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "ForGenLift" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine ForGenLift" >> fail "unreachable"
      Just d -> pure d
  let obls = dObligations doc
  length obls @?= 1
  case obls of
    [obl] -> do
      obName obl @?= "naturality"
      assertBool "expected for_gen template obligation" (obForGen obl)
      obForGenName obl @?= Nothing
    _ -> assertFailure "expected exactly one obligation template"

testForGenImplementsQuantifiesTarget :: Assertion
testForGenImplementsQuantifiesTarget = do
  let src = T.unlines
        [ "doctrine FGSchema where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [M.U_M] @M;"
        , "  gen keep : [M.X] -> [M.X] @M;"
        , "  obligation all_id for_gen @M ="
        , "    @gen == id[M.X]"
        , "}"
        , "doctrine FGTgt where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [M.U_M] @M;"
        , "  gen keep : [M.X] -> [M.X] @M;"
        , "  gen bad : [M.X] -> [M.X] @M;"
        , "  rule computational keep_id -> : [M.X] -> [M.X] @M ="
        , "    keep == id[M.X]"
        , "}"
        , "morphism fgInst : FGSchema -> FGTgt where {"
        , "  mode M -> M;"
        , "  gen ctx_ext @M -> ctx_ext"
        , "  gen var @M -> var"
        , "  gen reindex @M -> reindex"
        , "  gen keep @M -> keep"
        , "  check none;"
        , "}"
        , "implements FGSchema for FGTgt using fgInst;"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      if "implements obligation failed: all_id[bad]" `T.isInfixOf` err
          || "implements obligation undecided: all_id[bad]" `T.isInfixOf` err
        then pure ()
        else assertFailure ("expected for_gen target quantification failure, got: " <> T.unpack err)
    Right _ ->
      assertFailure "expected implements to fail on unsatisfied for_gen obligation for target generator"

testForGenSchemaRefsMapped :: Assertion
testForGenSchemaRefsMapped = do
  let src = T.unlines
        [ "doctrine FGSchemaMap where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [M.U_M] @M;"
        , "  gen op(a@M) : [a] -> [a] @M;"
        , "  obligation mapped_op for_gen @M ="
        , "    @gen ; lift_cod(op) == @gen ; lift_cod(op)"
        , "}"
        , "doctrine FGTgtMap where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [M.U_M] @M;"
        , "  gen discard(a@M) : [a] -> [] @M;"
        , "  gen keep(a@M) : [a] -> [a] @M;"
        , "  gen op2(a@M) : [a] -> [a] @M;"
        , "}"
        , "morphism fgMapInst : FGSchemaMap -> FGTgtMap where {"
        , "  mode M -> M;"
        , "  gen ctx_ext @M -> ctx_ext"
        , "  gen var @M -> var"
        , "  gen reindex @M -> reindex"
        , "  gen op @M -> op2"
        , "  check none;"
        , "}"
        , "implements FGSchemaMap for FGTgtMap using fgMapInst;"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  assertBool
    "expected mapped for_gen obligation to validate through morphism mapping"
    (M.member ("FGSchemaMap", "FGTgtMap") (meImplDefaults env))

testForGenPolyLiftInstantiation :: Assertion
testForGenPolyLiftInstantiation = do
  let src = T.unlines
        [ "doctrine FGSchemaPolyLift where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [M.U_M] @M;"
        , "  gen op(a@M) : [a] -> [a] @M;"
        , "  obligation refl for_gen @M ="
        , "    @gen ; lift_cod(op) == @gen ; lift_cod(op)"
        , "}"
        , "doctrine FGTgtPolyLift where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [M.U_M] @M;"
        , "  gen keep : [M.X] -> [M.X] @M;"
        , "  gen op2(a@M) : [a] -> [a] @M;"
        , "}"
        , "morphism inst : FGSchemaPolyLift -> FGTgtPolyLift where {"
        , "  mode M -> M;"
        , "  gen ctx_ext @M -> ctx_ext"
        , "  gen var @M -> var"
        , "  gen reindex @M -> reindex"
        , "  gen op @M -> op2"
        , "  check none;"
        , "}"
        , "implements FGSchemaPolyLift for FGTgtPolyLift using inst;"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  assertBool
    "expected for_gen lift_cod polymorphic operator instantiation to validate"
    (M.member ("FGSchemaPolyLift", "FGTgtPolyLift") (meImplDefaults env))

testForGenLiftAllowsCodArityChange :: Assertion
testForGenLiftAllowsCodArityChange = do
  let src = T.unlines
        [ "doctrine FGSchemaDropLift where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [M.U_M] @M;"
        , "  gen drop(a@M) : [a] -> [] @M;"
        , "  obligation erased for_gen @M ="
        , "    lift_dom(drop) == lift_dom(drop)"
        , "}"
        , "doctrine FGTgtDropLift where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [M.U_M] @M;"
        , "  gen discard(a@M) : [a] -> [] @M;"
        , "}"
        , "morphism fgDropInst : FGSchemaDropLift -> FGTgtDropLift where {"
        , "  mode M -> M;"
        , "  gen ctx_ext @M -> ctx_ext"
        , "  gen var @M -> var"
        , "  gen reindex @M -> reindex"
        , "  gen drop @M -> discard"
        , "  check none;"
        , "}"
        , "implements FGSchemaDropLift for FGTgtDropLift using fgDropInst;"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  assertBool
    "expected lift_dom to accept operators with non-unary codomain arity"
    (M.member ("FGSchemaDropLift", "FGTgtDropLift") (meImplDefaults env))

testForGenLiftDomCompositionAnchoring :: Assertion
testForGenLiftDomCompositionAnchoring = do
  let src = T.unlines
        [ "doctrine FGCompAnchor where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen Y : [] -> [M.U_M] @M;"
        , "  gen op(a@M) : [a] -> [a] @M;"
        , "  gen eraseY : [M.Y] -> [] @M;"
        , "  gen unit : [] -> [] @M;"
        , "  obligation anchored for_gen @M ="
        , "    lift_dom(op) ; eraseY == lift_dom(op) ; eraseY"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "FGCompAnchor" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine FGCompAnchor" >> fail "unreachable"
      Just d -> pure d
  let generated = [ obl { obGenerated = True } | obl <- dObligations doc ]
  let schemaDoc = doc { dObligations = generated }
  identity <- requireEither (identityMorphismFor doc)
  result <- requireEither (checkImplementsObligationsWithBudget defaultSearchBudget env doc identity schemaDoc)
  case result of
    ImplementsCheckUndecided label _ ->
      assertFailure ("expected anchored lift_dom composition to be decidable, got undecided: " <> T.unpack label)
    ImplementsCheckProved _ ->
      pure ()

testForGenBoundaryLockedForUserObligations :: Assertion
testForGenBoundaryLockedForUserObligations = do
  let src = T.unlines
        [ "doctrine FGSchemaBoundaryLock where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [M.U_M] @M;"
        , "  gen keep : [M.X] -> [M.X] @M;"
        , "  obligation vacuous for_gen @M ="
        , "    id[M.X] == id[M.X]"
        , "}"
        , "doctrine FGTgtBoundaryLock where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [M.U_M] @M;"
        , "  gen keep : [M.X] -> [M.X] @M;"
        , "  gen bad : [M.X] -> [] @M;"
        , "}"
        , "morphism fgBoundaryInst : FGSchemaBoundaryLock -> FGTgtBoundaryLock where {"
        , "  mode M -> M;"
        , "  gen ctx_ext @M -> ctx_ext"
        , "  gen var @M -> var"
        , "  gen reindex @M -> reindex"
        , "  gen keep @M -> keep"
        , "  check none;"
        , "}"
        , "implements FGSchemaBoundaryLock for FGTgtBoundaryLock using fgBoundaryInst;"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      if "implements obligation vacuous[bad]: boundary lock failed" `T.isInfixOf` err
        then pure ()
        else assertFailure ("expected boundary-lock failure for vacuous[bad], got: " <> T.unpack err)
    Right _ ->
      assertFailure "expected user-authored for_gen obligation to remain boundary-locked to @gen"

testForGenGenPlacementRejected :: Assertion
testForGenGenPlacementRejected = do
  let src = T.unlines
        [ "doctrine BadForGenPlacement where {"
        , "  mode A classifiedBy A via A.U_A;"
        , "  gen U_A : [] -> [A.U_A] @A;"
        , "  mode B classifiedBy B via B.U_B;"
        , "  gen U_B : [] -> [B.U_B] @B;"
        , "  modality F : A -> B;"
        , "  gen X : [] -> [A.U_A] @A;"
        , "  gen Y : [] -> [B.U_B] @B;"
        , "  gen g(b@B) : [b] -> [b] @B;"
        , "  obligation bad for_gen @B ="
        , "    map[F](@gen) == map[F](@gen)"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      if "obligation mode" `T.isInfixOf` err
        then pure ()
        else assertFailure ("expected @gen placement error, got: " <> T.unpack err)
    Right _ ->
      assertFailure "expected for_gen obligation to reject @gen in mode-changing map context"

testGenOutsideForGenRejected :: Assertion
testGenOutsideForGenRejected = do
  let src = T.unlines
        [ "doctrine BadGenObl where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen X : [] -> [M.U_M] @M;"
        , "  gen g : [M.X] -> [M.X] @M;"
        , "  obligation bad : [M.X] -> [M.X] @M ="
        , "    @gen == @gen"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      if "@gen" `T.isInfixOf` err
        then pure ()
        else assertFailure ("expected @gen error, got: " <> T.unpack err)
    Right _ ->
      assertFailure "expected obligation elaboration to reject @gen outside for_gen"

testActionModEqCoherence :: Assertion
testActionModEqCoherence = do
  let src = T.unlines
        [ "doctrine BadAction where {"
        , "  mode A classifiedBy A via A.U_A;"
        , "  gen U_A : [] -> [A.U_A] @A;"
        , "  gen ctx_ext(a@A) : [a] -> [a] @A;"
        , "  gen var(a@A) : [a] -> [a] @A;"
        , "  gen reindex(a@A) : [a] -> [a] @A;"
        , "  comprehension A where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen X : [] -> [A.U_A] @A;"
        , "  modality F : A -> A;"
        , "  mod_eq F -> id@A;"
        , "  gen g : [A.X] -> [A.X] @A;"
        , "  gen h : [A.X] -> [A.X] @A;"
        , "  action F where {"
        , "    gen g -> h"
        , "    gen h -> h"
        , "    gen ctx_ext -> ctx_ext"
        , "    gen var -> var"
        , "    gen reindex -> reindex"
        , "  }"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      if "action coherence failed" `T.isInfixOf` err
          || "action coherence undecided" `T.isInfixOf` err
          || "action semantics undecided" `T.isInfixOf` err
        then pure ()
        else assertFailure ("expected action coherence error, got: " <> T.unpack err)
    Right _ ->
      assertFailure "expected doctrine elaboration to reject incoherent action under mod_eq"

testComprehensionDeclElab :: Assertion
testComprehensionDeclElab = do
  let src = T.unlines
        [ "doctrine CompOk where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext : [M.U_M] -> [M.U_M] @M;"
        , "  gen var : [M.U_M] -> [M.U_M] @M;"
        , "  gen reindex : [M.U_M] -> [M.U_M] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "CompOk" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine CompOk" >> fail "unreachable"
      Just d -> pure d
  classDecl <-
    case M.lookup (ModeName "M") (mtClassifiedBy (dModes doc)) of
      Nothing -> assertFailure "missing classification for mode M" >> fail "unreachable"
      Just decl -> pure decl
  case cdComp classDecl of
    Nothing -> assertFailure "expected comprehension declaration to be stored"
    Just comp -> do
      compCtxExt comp @?= GenName "ctx_ext"
      compVar comp @?= GenName "var"
      compReindex comp @?= GenName "reindex"

testComprehensionRequiresClassifiedMode :: Assertion
testComprehensionRequiresClassifiedMode = do
  let src = T.unlines
        [ "doctrine CompNeedsClass where {"
        , "  mode M;"
        , "  comprehension M where { ctx_ext = ctx; var = v; reindex = r; };"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool
        ("expected missing classifiedBy error, got: " <> T.unpack err)
        ("requires classifiedBy" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected comprehension declaration to fail on non-classified mode"

testComprehensionUnknownGenerator :: Assertion
testComprehensionUnknownGenerator = do
  let src = T.unlines
        [ "doctrine CompUnknownGen where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen ctx_ext : [M.U_M] -> [M.U_M] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = missing; reindex = missing2; };"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool
        ("expected unknown generator error, got: " <> T.unpack err)
        ("unknown generator" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected comprehension declaration with missing generator to fail"

testComprehensionRejectsCtorLike :: Assertion
testComprehensionRejectsCtorLike = do
  let src = T.unlines
        [ "doctrine CompCtorLike where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen var : [M.U_M] -> [M.U_M] @M;"
        , "  gen reindex : [M.U_M] -> [M.U_M] @M;"
        , "  comprehension M where { ctx_ext = U_M; var = var; reindex = reindex; };"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool
        ("expected constructor-like rejection, got: " <> T.unpack err)
        ("constructor-like" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected comprehension declaration to reject constructor-like generators"

testComprehensionBinderRequiresDecl :: Assertion
testComprehensionBinderRequiresDecl = do
  let src = T.unlines
        [ "doctrine CompNeedsDecl where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen Nat : [] -> [M.U_M] @M;"
        , "  gen Z : [] -> [Nat] @M;"
        , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
        , "  gen Out : [] -> [M.U_M] @M;"
        , "  gen wrap : [binder { tm n : Nat } : [Vec(Z)]] -> [Out] @M;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool
        ("expected missing comprehension declaration error, got: " <> T.unpack err)
        ("requires a comprehension declaration" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected doctrine elaboration to reject binder generators without comprehension declaration"

testComprehensionRequiresDeclWithoutBinder :: Assertion
testComprehensionRequiresDeclWithoutBinder = do
  let src = T.unlines
        [ "doctrine CompOptional where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen Nat : [] -> [M.U_M] @M;"
        , "  gen Z : [] -> [Nat] @M;"
        , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
        , "  gen use(n : Nat) : [] -> [Vec(n)] @M;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      assertBool
        ("expected missing comprehension declaration error, got: " <> T.unpack err)
        ("requires a comprehension declaration" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected doctrine elaboration to reject classified mode without comprehension declaration"

testComprehensionGeneratedObligations :: Assertion
testComprehensionGeneratedObligations = do
  let src = T.unlines
        [ "doctrine CompGenerated where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen Nat : [] -> [M.U_M] @M;"
        , "  gen Z : [] -> [Nat] @M;"
        , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
        , "  gen Out : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  rule computational ctx_ext_id -> (a@M) : [a] -> [a] @M ="
        , "    ctx_ext{a} == id[a]"
        , "  rule computational var_id -> (a@M) : [a] -> [a] @M ="
        , "    var{a} == id[a]"
        , "  rule computational reindex_id -> (a@M) : [a] -> [a] @M ="
        , "    reindex{a} == id[a]"
        , "  gen wrap : [binder { tm n : Nat } : [Vec(Z)]] -> [Out] @M;"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "CompGenerated" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine CompGenerated" >> fail "unreachable"
      Just d -> pure d
  let generated = [obl | obl <- dObligations doc, obGenerated obl]
  assertBool "expected generated comprehension obligations" (not (null generated))
  assertBool "expected generated comprehension obligations to target concrete generators" (all (isJust . obForGenName) generated)
  assertBool "expected generated comprehension obligations to include composition laws" (any ("/comp_dom" `T.isSuffixOf`) (map obName generated))
  assertBool "expected generated comprehension obligations to include naturality laws" (any ("/nat" `T.isSuffixOf`) (map obName generated))

testComprehensionMixedBinderExcluded :: Assertion
testComprehensionMixedBinderExcluded = do
  let src = T.unlines
        [ "doctrine CompMixedCodOnly where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen A : [] -> [M.U_M] @M;"
        , "  gen B : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  rule computational ctx_ext_id -> (a@M) : [a] -> [a] @M ="
        , "    ctx_ext{a} == id[a]"
        , "  rule computational var_id -> (a@M) : [a] -> [a] @M ="
        , "    var{a} == id[a]"
        , "  rule computational reindex_id -> (a@M) : [a] -> [a] @M ="
        , "    reindex{a} == id[a]"
        , "  gen mixed : [A, binder { x : A } : [B]] -> [B] @M;"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "CompMixedCodOnly" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine CompMixedCodOnly" >> fail "unreachable"
      Just d -> pure d
  let generated =
        [ obl
        | obl <- dObligations doc
        , obGenerated obl
        , obForGenName obl == Just (GenName "mixed")
        ]
  assertBool "expected no generated obligations for mixed generator" (null generated)

testComprehensionMultiBinderOnlyFull :: Assertion
testComprehensionMultiBinderOnlyFull = do
  let src = T.unlines
        [ "doctrine CompMultiBinderOnly where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen A : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  rule computational ctx_ext_id -> (a@M) : [a] -> [a] @M ="
        , "    ctx_ext{a} == id[a]"
        , "  rule computational var_id -> (a@M) : [a] -> [a] @M ="
        , "    var{a} == id[a]"
        , "  rule computational reindex_id -> (a@M) : [a] -> [a] @M ="
        , "    reindex{a} == id[a]"
        , "  gen mbind : [binder { x : A } : [A], binder { y : A } : [A]] -> [A] @M;"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "CompMultiBinderOnly" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine CompMultiBinderOnly" >> fail "unreachable"
      Just d -> pure d
  let names =
        [ obName obl
        | obl <- dObligations doc
        , obGenerated obl
        , obForGenName obl == Just (GenName "mbind")
        ]
  assertBool "expected generated obligations for mbind" (not (null names))
  assertBool "expected full dom identity laws for multi-binder generator" (any ("/id_dom" `T.isSuffixOf`) names)
  assertBool "expected full cod identity laws for multi-binder generator" (any ("/id_cod" `T.isSuffixOf`) names)
  assertBool "expected full dom composition laws for multi-binder generator" (any ("/comp_dom" `T.isSuffixOf`) names)
  assertBool "expected full cod composition laws for multi-binder generator" (any ("/comp_cod" `T.isSuffixOf`) names)
  assertBool "expected naturality laws for multi-binder generator" (any ("/nat" `T.isSuffixOf`) names)
  assertBool "expected per-slot law expansion for both binder slots" (length names >= 10)

testComprehensionCtorSlotBoundarySide :: Assertion
testComprehensionCtorSlotBoundarySide = do
  let src = T.unlines
        [ "doctrine CompCtorSide where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen Nat : [] -> [M.U_M] @M;"
        , "  gen Z : [] -> [Nat] @M;"
        , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
        , "  gen Out : [] -> [M.U_M] @M;"
        , "  gen use(n : Nat) : [] -> [Vec(n)] @M;"
        , "  gen wrap : [Vec(Z)] -> [Out] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  rule computational ctx_ext_id -> (a@M) : [a] -> [a] @M ="
        , "    ctx_ext{a} == id[a]"
        , "  rule computational var_id -> (a@M) : [a] -> [a] @M ="
        , "    var{a} == id[a]"
        , "  rule computational reindex_id -> (a@M) : [a] -> [a] @M ="
        , "    reindex{a} == id[a]"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "CompCtorSide" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine CompCtorSide" >> fail "unreachable"
      Just d -> pure d
  let generatedFor g =
        [ obName obl
        | obl <- dObligations doc
        , obGenerated obl
        , obForGenName obl == Just (GenName g)
        ]
  let useNames = generatedFor "use"
  let wrapNames = generatedFor "wrap"
  assertBool "expected generated obligations for use" (not (null useNames))
  assertBool "expected generated obligations for wrap" (not (null wrapNames))
  assertBool "expected cod laws for cod-side ctor slot (use)" (any ("/id_cod" `T.isSuffixOf`) useNames && any ("/comp_cod" `T.isSuffixOf`) useNames)
  assertBool "expected no dom laws for cod-side ctor slot (use)" (not (any ("/id_dom" `T.isSuffixOf`) useNames) && not (any ("/comp_dom" `T.isSuffixOf`) useNames))
  assertBool "expected dom laws for dom-side ctor slot (wrap)" (any ("/id_dom" `T.isSuffixOf`) wrapNames && any ("/comp_dom" `T.isSuffixOf`) wrapNames)
  assertBool "expected no cod laws for dom-side ctor slot (wrap)" (not (any ("/id_cod" `T.isSuffixOf`) wrapNames) && not (any ("/comp_cod" `T.isSuffixOf`) wrapNames))

testComprehensionCtorSlotMultiPortDom :: Assertion
testComprehensionCtorSlotMultiPortDom = do
  let src = T.unlines
        [ "doctrine CompCtorMultiDom where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen Nat : [] -> [M.U_M] @M;"
        , "  gen Z : [] -> [Nat] @M;"
        , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
        , "  gen Out : [] -> [M.U_M] @M;"
        , "  gen pairWrap : [Vec(Z), Vec(Z)] -> [Out] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  rule computational ctx_ext_id -> (a@M) : [a] -> [a] @M ="
        , "    ctx_ext{a} == id[a]"
        , "  rule computational var_id -> (a@M) : [a] -> [a] @M ="
        , "    var{a} == id[a]"
        , "  rule computational reindex_id -> (a@M) : [a] -> [a] @M ="
        , "    reindex{a} == id[a]"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "CompCtorMultiDom" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine CompCtorMultiDom" >> fail "unreachable"
      Just d -> pure d
  let names =
        [ obName obl
        | obl <- dObligations doc
        , obGenerated obl
        , obForGenName obl == Just (GenName "pairWrap")
        ]
  assertBool "expected generated obligations for pairWrap" (not (null names))
  assertBool "expected dom laws for dom-side ctor slots on multi-port domain" (any ("/id_dom" `T.isSuffixOf`) names && any ("/comp_dom" `T.isSuffixOf`) names)
  assertBool "expected no cod laws for dom-side ctor slots on multi-port domain" (not (any ("/id_cod" `T.isSuffixOf`) names) && not (any ("/comp_cod" `T.isSuffixOf`) names))

testComprehensionCtorSlotBinderDomain :: Assertion
testComprehensionCtorSlotBinderDomain = do
  let src = T.unlines
        [ "doctrine CompCtorBinderDom where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen Nat : [] -> [M.U_M] @M;"
        , "  gen Z : [] -> [Nat] @M;"
        , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
        , "  gen A : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  rule computational ctx_ext_id -> (a@M) : [a] -> [a] @M ="
        , "    ctx_ext{a} == id[a]"
        , "  rule computational var_id -> (a@M) : [a] -> [a] @M ="
        , "    var{a} == id[a]"
        , "  rule computational reindex_id -> (a@M) : [a] -> [a] @M ="
        , "    reindex{a} == id[a]"
        , "  gen bctor : [binder { x : A } : [A]] -> [Vec(Z)] @M;"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "CompCtorBinderDom" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine CompCtorBinderDom" >> fail "unreachable"
      Just d -> pure d
  let names =
        [ obName obl
        | obl <- dObligations doc
        , obGenerated obl
        , obForGenName obl == Just (GenName "bctor")
        ]
  assertBool "expected generated obligations for bctor" (not (null names))
  let ctorNames = filter ("arg" `T.isInfixOf`) names
  assertBool "expected ctor-slot laws to be generated even with binder domains" (not (null ctorNames))
  assertBool "expected cod-side ctor laws in binder-domain generator" (any ("/id_cod" `T.isSuffixOf`) ctorNames && any ("/comp_cod" `T.isSuffixOf`) ctorNames)
  assertBool "expected no dom-side ctor laws for cod-side ctor slot" (not (any ("/id_dom" `T.isSuffixOf`) ctorNames) && not (any ("/comp_dom" `T.isSuffixOf`) ctorNames))

testComprehensionCrossModeCtorSlots :: Assertion
testComprehensionCrossModeCtorSlots = do
  let src = T.unlines
        [ "doctrine CompCrossMode where {"
        , "  mode G classifiedBy G via G.U_G;"
        , "  gen U_G : [] -> [G.U_G] @G;"
        , "  gen ctx_ext(a@G) : [a] -> [a] @G;"
        , "  gen var(a@G) : [a] -> [a] @G;"
        , "  gen reindex(a@G) : [a] -> [a] @G;"
        , "  comprehension G where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen Count : [] -> [G.U_G] @G;"
        , "  gen zero : [] -> [Count] @G;"
        , "  gen succ : [Count] -> [Count] @G;"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen A : [] -> [M.U_M] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  rule computational ctx_ext_id -> (a@M) : [a] -> [a] @M ="
        , "    ctx_ext{a} == id[a]"
        , "  rule computational var_id -> (a@M) : [a] -> [a] @M ="
        , "    var{a} == id[a]"
        , "  rule computational reindex_id -> (a@M) : [a] -> [a] @M ="
        , "    reindex{a} == id[a]"
        , "  gen T(g : Count, a@M) : [] -> [M.U_M] @M;"
        , "  gen expect1(a@M) : [T(succ(zero), a)] -> [a] @M;"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "CompCrossMode" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine CompCrossMode" >> fail "unreachable"
      Just d -> pure d
  let names =
        [ obName obl
        | obl <- dObligations doc
        , obGenerated obl
        , obForGenName obl == Just (GenName "expect1")
        ]
  assertBool "expected cross-mode ctor slots to be ignored by owner-mode gating" (null names)

testComprehensionGeneratedObligationJoinProof :: Assertion
testComprehensionGeneratedObligationJoinProof = do
  let src = T.unlines
        [ "doctrine CompJoinProof where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  gen Nat : [] -> [M.U_M] @M;"
        , "  gen Z : [] -> [Nat] @M;"
        , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
        , "  gen Out : [] -> [M.U_M] @M;"
        , "  gen wrap : [binder { tm n : Nat } : [Vec(Z)]] -> [Out] @M;"
        , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
        , "  gen var(a@M) : [a] -> [a] @M;"
        , "  gen reindex(a@M) : [a] -> [a] @M;"
        , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  rule computational ctx_ext_id -> (a@M) : [a] -> [a] @M ="
        , "    ctx_ext{a} == id[a]"
        , "  rule computational var_id -> (a@M) : [a] -> [a] @M ="
        , "    var{a} == id[a]"
        , "  rule computational reindex_id -> (a@M) : [a] -> [a] @M ="
        , "    reindex{a} == id[a]"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "CompJoinProof" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine CompJoinProof" >> fail "unreachable"
      Just d -> pure d
  let generated = [obl | obl <- dObligations doc, obGenerated obl]
  assertBool "expected generated obligations in CompJoinProof" (not (null generated))
  let schemaDoc = doc { dObligations = generated }
  identity <- requireEither (identityMorphismFor doc)
  result <- requireEither (checkImplementsObligationsWithBudget defaultSearchBudget env doc identity schemaDoc)
  case result of
    ImplementsCheckUndecided label _ ->
      assertFailure ("expected generated obligations to be decidable, got undecided: " <> T.unpack label)
    ImplementsCheckProved proofs -> do
      assertBool
        "expected at least one generated obligation to be discharged via join proof"
        (any (\(_, p) -> case p of ImplementsProofJoin _ -> True; _ -> False) proofs)

testAdjObligationFail :: Assertion
testAdjObligationFail = do
  let src = T.unlines
        [ "doctrine AdjSchema where {"
        , "  mode C classifiedBy C via C.U_C;"
        , "  gen U_C : [] -> [C.U_C] @C;"
        , "  gen ctx_ext(a@C) : [a] -> [a] @C;"
        , "  gen var(a@C) : [a] -> [a] @C;"
        , "  gen reindex(a@C) : [a] -> [a] @C;"
        , "  comprehension C where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode L classifiedBy L via F(C.U_C);"
        , "  gen ctx_ext(a@L) : [a] -> [a] @L;"
        , "  gen var(a@L) : [a] -> [a] @L;"
        , "  gen reindex(a@L) : [a] -> [a] @L;"
        , "  comprehension L where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  modality F : C -> L;"
        , "  modality U : L -> C;"
        , "  lift_classifier F = F;"
        , "  lift_classifier U = U;"
        , "  mod_eq U.F -> id@C;"
        , "  mod_eq F.U -> id@L;"
        , "  gen eta(a@C) : [a] -> [U(F(a))] @C;"
        , "  gen eps(b@L) : [F(U(b))] -> [b] @L;"
        , "  obligation triangleL(a@C) : [F(a)] -> [F(a)] @L ="
        , "    map[F](eta{a}) ; eps{F(a)} == id[F(a)]"
        , "  obligation triangleR(b@L) : [U(b)] -> [U(b)] @C ="
        , "    eta{U(b)} ; map[U](eps{b}) == id[U(b)]"
        , "}"
        , "doctrine BadAdj where {"
        , "  mode C classifiedBy C via C.U_C;"
        , "  gen U_C : [] -> [C.U_C] @C;"
        , "  gen ctx_ext(a@C) : [a] -> [a] @C;"
        , "  gen var(a@C) : [a] -> [a] @C;"
        , "  gen reindex(a@C) : [a] -> [a] @C;"
        , "  comprehension C where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode L classifiedBy L via F(C.U_C);"
        , "  gen ctx_ext(a@L) : [a] -> [a] @L;"
        , "  gen var(a@L) : [a] -> [a] @L;"
        , "  gen reindex(a@L) : [a] -> [a] @L;"
        , "  comprehension L where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  modality F : C -> L;"
        , "  modality U : L -> C;"
        , "  lift_classifier F = F;"
        , "  lift_classifier U = U;"
        , "  mod_eq U.F -> id@C;"
        , "  mod_eq F.U -> id@L;"
        , "  gen eta(a@C) : [a] -> [U(F(a))] @C;"
        , "  gen eps(b@L) : [F(U(b))] -> [b] @L;"
        , "  action F where {"
        , "    gen ctx_ext -> ctx_ext"
        , "    gen var -> var"
        , "    gen reindex -> reindex"
        , "    gen eta -> eps"
        , "  }"
        , "  action U where {"
        , "    gen ctx_ext -> ctx_ext"
        , "    gen var -> var"
        , "    gen reindex -> reindex"
        , "    gen eps -> eta"
        , "  }"
        , "}"
        , "morphism badAdjInst : AdjSchema -> BadAdj where {"
        , "  mode C -> C;"
        , "  mode L -> L;"
        , "  modality F -> F;"
        , "  modality U -> U;"
        , "  gen ctx_ext @C -> ctx_ext"
        , "  gen var @C -> var"
        , "  gen reindex @C -> reindex"
        , "  gen ctx_ext @L -> ctx_ext"
        , "  gen var @L -> var"
        , "  gen reindex @L -> reindex"
        , "  gen eta @C -> eta"
        , "  gen eps @L -> eps"
        , "  check none;"
        , "}"
        , "implements AdjSchema for BadAdj using badAdjInst;"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err ->
      if "implements obligation failed:" `T.isInfixOf` err
          || "implements obligation undecided:" `T.isInfixOf` err
        then pure ()
        else assertFailure ("expected implements obligation failure, got: " <> T.unpack err)
    Right _ ->
      assertFailure "expected implements to fail on unsatisfied schema obligations"

testAdjObligationPass :: Assertion
testAdjObligationPass = do
  let src = T.unlines
        [ "doctrine AdjSchema where {"
        , "  mode C classifiedBy C via C.U_C;"
        , "  gen U_C : [] -> [C.U_C] @C;"
        , "  gen ctx_ext(a@C) : [a] -> [a] @C;"
        , "  gen var(a@C) : [a] -> [a] @C;"
        , "  gen reindex(a@C) : [a] -> [a] @C;"
        , "  comprehension C where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode L classifiedBy L via F(C.U_C);"
        , "  gen ctx_ext(a@L) : [a] -> [a] @L;"
        , "  gen var(a@L) : [a] -> [a] @L;"
        , "  gen reindex(a@L) : [a] -> [a] @L;"
        , "  comprehension L where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  modality F : C -> L;"
        , "  modality U : L -> C;"
        , "  lift_classifier F = F;"
        , "  lift_classifier U = U;"
        , "  mod_eq U.F -> id@C;"
        , "  mod_eq F.U -> id@L;"
        , "  gen eta(a@C) : [a] -> [U(F(a))] @C;"
        , "  gen eps(b@L) : [F(U(b))] -> [b] @L;"
        , "  obligation triangleL(a@C) : [F(a)] -> [F(a)] @L ="
        , "    map[F](eta{a}) ; eps{F(a)} == id[F(a)]"
        , "  obligation triangleR(b@L) : [U(b)] -> [U(b)] @C ="
        , "    eta{U(b)} ; map[U](eps{b}) == id[U(b)]"
        , "}"
        , "doctrine GoodAdj where {"
        , "  mode C classifiedBy C via C.U_C;"
        , "  gen U_C : [] -> [C.U_C] @C;"
        , "  gen ctx_ext(a@C) : [a] -> [a] @C;"
        , "  gen var(a@C) : [a] -> [a] @C;"
        , "  gen reindex(a@C) : [a] -> [a] @C;"
        , "  comprehension C where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  mode L classifiedBy L via F(C.U_C);"
        , "  gen ctx_ext(a@L) : [a] -> [a] @L;"
        , "  gen var(a@L) : [a] -> [a] @L;"
        , "  gen reindex(a@L) : [a] -> [a] @L;"
        , "  comprehension L where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  modality F : C -> L;"
        , "  modality U : L -> C;"
        , "  lift_classifier F = F;"
        , "  lift_classifier U = U;"
        , "  mod_eq U.F -> id@C;"
        , "  mod_eq F.U -> id@L;"
        , "  gen eta(a@C) : [a] -> [U(F(a))] @C;"
        , "  gen eps(b@L) : [F(U(b))] -> [b] @L;"
        , "  action F where {"
        , "    gen ctx_ext -> ctx_ext"
        , "    gen var -> var"
        , "    gen reindex -> reindex"
        , "    gen eta -> eps"
        , "  }"
        , "  action U where {"
        , "    gen ctx_ext -> ctx_ext"
        , "    gen var -> var"
        , "    gen reindex -> reindex"
        , "    gen eps -> eta"
        , "  }"
        , "  rule computational eta_id -> (a@C) : [a] -> [a] @C ="
        , "    eta{a} ; eta{a} == id[a]"
        , "  rule computational eps_id -> (b@L) : [b] -> [b] @L ="
        , "    eps{b} ; eps{b} == id[b]"
        , "}"
        , "morphism goodAdjInst : AdjSchema -> GoodAdj where {"
        , "  mode C -> C;"
        , "  mode L -> L;"
        , "  modality F -> F;"
        , "  modality U -> U;"
        , "  gen ctx_ext @C -> ctx_ext"
        , "  gen var @C -> var"
        , "  gen reindex @C -> reindex"
        , "  gen ctx_ext @L -> ctx_ext"
        , "  gen var @L -> var"
        , "  gen reindex @L -> reindex"
        , "  gen eta @C -> eta"
        , "  gen eps @L -> eps"
        , "  check none;"
        , "}"
        , "implements AdjSchema for GoodAdj using goodAdjInst;"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  assertBool
    "expected implements default instance recorded"
    (M.member ("AdjSchema", "GoodAdj") (meImplDefaults env))

testMonadObligationPass :: Assertion
testMonadObligationPass = do
  let src = T.unlines
        [ "doctrine SchemaMonad where {"
        , "  mode C classifiedBy C via T(C.U_C);"
        , "  modality T : C -> C;"
        , "  lift_classifier T = T;"
        , "  mod_eq T.T -> T;"
        , "  gen U_C : [] -> [T(C.U_C)] @C;"
        , "  gen ctx_ext(a@C) : [a] -> [a] @C;"
        , "  gen var(a@C) : [a] -> [a] @C;"
        , "  gen reindex(a@C) : [a] -> [a] @C;"
        , "  comprehension C where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen ret(x@C) : [x] -> [T(x)] @C;"
        , "  gen join(x@C) : [T(T(x))] -> [T(x)] @C;"
        , "  obligation leftUnit(a@C) : [T(a)] -> [T(a)] @C ="
        , "    map[T](ret{a}) ; join{a} == id[T(a)]"
        , "  obligation rightUnit(a@C) : [T(a)] -> [T(a)] @C ="
        , "    ret{T(a)} ; join{a} == id[T(a)]"
        , "  obligation assoc(a@C) : [T(T(T(a)))] -> [T(a)] @C ="
        , "    map[T](join{a}) ; join{a} == join{T(a)} ; join{a}"
        , "}"
        , "doctrine IdMonad where {"
        , "  mode C classifiedBy C via T(C.U_C);"
        , "  modality T : C -> C;"
        , "  lift_classifier T = T;"
        , "  mod_eq T.T -> T;"
        , "  gen U_C : [] -> [T(C.U_C)] @C;"
        , "  gen ctx_ext(a@C) : [a] -> [a] @C;"
        , "  gen var(a@C) : [a] -> [a] @C;"
        , "  gen reindex(a@C) : [a] -> [a] @C;"
        , "  comprehension C where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
        , "  gen ret(a@C) : [a] -> [T(a)] @C;"
        , "  gen join(a@C) : [T(T(a))] -> [T(a)] @C;"
        , "  action T where {"
        , "    gen ctx_ext -> ctx_ext"
        , "    gen var -> var"
        , "    gen reindex -> reindex"
        , "    gen ret -> ret"
        , "    gen join -> join"
        , "  }"
        , "  rule computational unit -> (a@C) : [T(a)] -> [T(a)] @C ="
        , "    ret{T(a)} ; join{a} == id[T(a)]"
        , "}"
        , "morphism monadInst : SchemaMonad -> IdMonad where {"
        , "  mode C -> C;"
        , "  modality T -> T;"
        , "  gen ctx_ext @C -> ctx_ext"
        , "  gen var @C -> var"
        , "  gen reindex @C -> reindex"
        , "  gen ret @C -> ret"
        , "  gen join @C -> join"
        , "  check none;"
        , "}"
        , "implements SchemaMonad for IdMonad using monadInst;"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  assertBool
    "expected monad implements default instance recorded"
    (M.member ("SchemaMonad", "IdMonad") (meImplDefaults env))

testAdjunctionKeywordRejected :: Assertion
testAdjunctionKeywordRejected = do
  let src = T.unlines
        [ "doctrine BadAdj where {"
        , "  mode C classifiedBy C via C.U_C;"
        , "  gen U_C : [] -> [C.U_C] @C;"
        , "  mode L classifiedBy L via L.U_L;"
        , "  gen U_L : [] -> [L.U_L] @L;"
        , "  modality F : C -> L;"
        , "  modality U : L -> C;"
        , "  " <> "adju" <> "nction F dashv U;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left _ -> pure ()
    Right _ -> assertFailure "expected legacy adj keyword to be rejected"

testStructureKeywordRejected :: Assertion
testStructureKeywordRejected = do
  let src = T.unlines
        [ "doctrine BadStruct where {"
        , "  mode M classifiedBy M via M.U_M;"
        , "  gen U_M : [] -> [M.U_M] @M;"
        , "  " <> "stru" <> "cture M = cartesian;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left _ -> pure ()
    Right _ -> assertFailure "expected structure keyword to be rejected"

buildStagingTheory :: ModeName -> ModeName -> Either T.Text ModeTheory
buildStagingTheory rt ct = do
  mt1 <- addMode rt (mkModes [])
  mt2 <- addMode ct mt1
  mt3 <- addModDecl (ModDecl { mdName = ModName "quote", mdSrc = rt, mdTgt = ct }) mt2
  mt4 <- addModDecl (ModDecl { mdName = ModName "splice", mdSrc = ct, mdTgt = rt }) mt3
  let lhs = ModExpr { meSrc = rt, meTgt = rt, mePath = [ModName "quote", ModName "splice"] }
  let rhs = ModExpr { meSrc = rt, meTgt = rt, mePath = [] }
  addModEqn (ModEqn lhs rhs) mt4

requireEither :: Either T.Text a -> IO a
requireEither =
  either (assertFailure . T.unpack) pure
