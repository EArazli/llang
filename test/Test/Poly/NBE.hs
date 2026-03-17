{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Test.Poly.NBE
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (ModuleEnv(..), emptyEnv)
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , BinderSig(..)
  , InputShape(..)
  , GenParam(..)
  , GenDecl(..)
  , BuiltinDecl(..)
  , BuiltinSpec(..)
  , BuiltinBranchDecl(..)
  , ModAction(..)
  , deriveCtorTables
  , genericGenDiagram
  , doctrineTypeTheory
  , validateDoctrine
  )
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Poly.DSL.Elab.Diag (elabRuleLHS, elabRuleRHS)
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.ModeTheory
  ( ModeTheory
  , ModeName(..)
  , ModName(..)
  , ModExpr(..)
  , ModDecl(..)
  , CompDecl(..)
  , ClassificationDecl(..)
  , emptyModeTheory
  , addMode
  , addModDecl
  , addClassification
  , addClassifierLift
  )
import Strat.Poly.TypeTheory
  ( TypeTheory
  , ExtensionalBuiltin(..)
  , EliminatorBuiltin(..)
  , RecursiveHeadArgSource(..)
  , BranchInputSource(..)
  , ElimBranchBuiltin(..)
  , InductiveElimBuiltin(..)
  , compiledRulesForMode
  , FunctionBuiltin(..)
  , eliminatorBuiltinForMode
  , extensionalBuiltinForMode
  , TmHeadSig(..)
  , functionBuiltinForMode
  , lookupTmHeadSig
  , modeOnlyTypeTheory
  , setModeCompiledRules
  , setModeDiagramRules
  , setModeTermHeads
  )
import Strat.Poly.Obj
  ( Obj
  , ObjName(..)
  , ObjRef(..)
  , TmVar(..)
  , TermDiagram(..)
  , CodeArg(..)
  , pattern OMod
  , unTerm
  , mkCon
  )
import Strat.Poly.DefEq (defEqRuleTermDiagramWithMapper, diagramToTermExprChecked, normalizeObjDeepWithCtx, normalizeTermDiagram, normalizeTermDiagramWithMapper, termExprToDiagramChecked)
import Strat.Poly.ModAction (ActionSemanticsProof(..), ActionSemanticsResult(..), applyAction, applyModExpr, validateActionSemanticsWithBudgetResult)
import Strat.Poly.Term.AST (TermHeadArg(..))
import Strat.Poly.TermExpr (TermExpr(..), TermBinderArg(..), termExprToDiagram, diagramToTermExpr, instantiateHostBoundCtx, structuralConvEnv)
import qualified Strat.Poly.Term.RewriteSystem as TRS
import Strat.Poly.Graph
  ( Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  , BinderArg(..)
  , BinderMetaVar(..)
  , emptyDiagram
  , freshPort
  , addEdgePayload
  , validateDiagram
  )
import Strat.Poly.Diagram (idDTm)
import Strat.Poly.DiagramIso (diagramIsoEq)
import Strat.Poly.Names (BoxName(..), GenName(..))
import Strat.Common.Rules (Orientation(..), RewritePolicy(..), RuleClass(..))
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Proof (defaultSearchBudget)
import Test.Poly.Helpers (mkModes, withZeroParamGenArgSigs)


tests :: TestTree
tests =
  testGroup
    "Poly.NBE"
    [ testCase "modes with function-space structure install builtins" testModeDeclInstallsFunctionBuiltins
    , testCase "builtin transport heads infer from defeq and erase on both canonical and neutral inputs" testBuiltinTransportEliminator
    , testCase "checked term conversion accepts builtin transport heads across defeq-equal input sorts" testCheckedBuiltinTransportConversion
    , testCase "data-macro folds infer as constructor eliminators and compute semantically" testBuiltinFoldEliminator
    , testCase "stuck builtin folds quote back deterministically through head eliminator frames" testBuiltinFoldNeutralResidual
    , testCase "constructor eliminators infer term parameters and nonzero scrutinee indices" testCtorElimTermParamsAndScrutineeIndex
    , testCase "constructor eliminators can source binder tmctx from outer term parameters" testCtorElimBinderTmCtxFromOuterHead
    , testCase "shared host-bound term substitution instantiates dependent context sorts" testCtorElimDependentBinderTmCtx
    , testCase "explicit builtin declarations elaborate through the surface syntax" testExplicitBuiltinSurfaceDecls
    , testCase "explicit builtin declarations reject branch source sort mismatches at doctrine build" testExplicitBuiltinSurfaceRejectsSortMismatch
    , testCase "explicit builtin eliminators resolve same-sort binder-source ambiguity" testExplicitBuiltinElimSameSortBinderSource
    , testCase "inferred builtin eliminators use rhs splice-hole identity instead of rule order" testInferredBuiltinElimUsesSpliceHoleIdentity
    , testCase "inferred builtin eliminators reject conflicting rhs splice-hole evidence" testInferredBuiltinElimRejectsConflictingHoleEvidence
    , testCase "nonzero-scrutinee constructor eliminators residualize through head frames" testCtorElimNonzeroScrutineeResidual
    , testCase "NbE beta: app(lam(\\x. x), t) normalizes to t" testNBEBeta
    , testCase "NbE eta: function variable normalizes to eta-long form" testNBEEta
    , testCase "NbE nested binders avoid capture" testNBENestedBinders
    , testCase "unified defeq mixes beta and trusted user rules in one run" testMixedBuiltinAndRewrite
    , testCase "shared term readers reject ill-typed binder-free residual heads" testResidualHeadSortMismatchRejected
    , testCase "binder heads live in the unified head table and enforce binder arity" testBinderHeadSignatureAndArity
    , testCase "opaque non-lambda binder heads residualize without crashing" testOpaqueBinderResidual
    , testCase "binder-bearing TermExpr heads roundtrip through checked diagrams" testBinderTermExprRoundtrip
    , testCase "trusted rewrite rules can build and match binder-bearing heads" testBinderRewriteRules
    , testCase "trusted rewrite RHS builtin lambdas re-enter builtin semantics" testRewriteProducesBuiltinLambda
    , testCase "trusted rewrite binder holes and rhs splices evaluate through the unified kernel path" testTrustedBinderSpliceRewrite
    , testCase "action semantics validation falls back to kernel defeq for mapped open-splice term rules" testActionSemanticsKernelFallback
    , testCase "trusted rewrite rhs splices honor modality actions through the unified kernel path" testTrustedModalSpliceRewrite
    , testCase "diagram-backed trusted RHSs execute through the unified kernel path" testDiagramBackedRewriteRHS
    , testCase "kernel defeq rewrites structural computational rules down to plain term normal forms" testKernelStructuralToTermNormalization
    , testCase "kernel defeq returns structurally normalized term diagrams when boxes remain" testKernelStructuralResidualNormalization
    , testCase "builtin heads cannot also carry trusted user rewrite rules" testBuiltinRewriteOverlapRejected
    , testCase "NbE mode missing lam is rejected at doctrine build" testNBEMissingLamRejected
    , testCase "NbE residualizes splice payloads in definitional normalization" testNBEResidualizesSplice
    , testCase "deriveCtorTables uses NbE for constructor eligibility" testCtorEligibilityUsesNBE
    , testCase "deriveCtorTables excludes non-defeq eligibility candidates without admitting them" testCtorEligibilityDefEqExclusion
    , testCase "deriveCtorTables rejects malformed NbE lam config at eligibility validation time" testCtorEligibilityLamShapeRejected
    , testCase "doctrineTypeTheory rejects NbE mode missing Arr constructor" testCtorEligibilityMissingArrRejected
    , testCase "NbE normalization accepts definitionally equal output sorts" testNBEOutputSortDefEq
    , testCase "CATm object arguments normalize through the unified evaluator" testCATmObjectNormalization
    , testCase "meta spines support non-prefix arguments and remain stable through NbE" testMetaSpineNonPrefixStable
    , testCase "stuck neutral applications residualize deterministically through eliminator frames" testNeutralElimFrameResidual
    , testCase "TRS mode still enforces termination checks" testTRSStillChecked
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

lookupDoctrineByName :: Text -> ModuleEnv -> IO Doctrine
lookupDoctrineByName name env =
  case M.lookup name (meDoctrines env) of
    Nothing -> assertFailure ("missing doctrine: " <> T.unpack name) >> fail "unreachable"
    Just d -> pure d

modeM :: ModeName
modeM = ModeName "M"

modeI :: ModeName
modeI = ModeName "I"

arrTy :: Obj -> Obj -> Obj
arrTy domTy codTy =
  mkCon
    (ObjRef modeM (ObjName "Arr"))
    [ CAObj domTy
    , CAObj codTy
    ]

mkNbeTypeTheory :: IO (TypeTheory, Obj, Obj)
mkNbeTypeTheory = do
  env <- require (parseRawFile nbeDoctrineSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "NBEMode" env
  tt <- require (doctrineTypeTheory doc)
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  let bTy = mkCon (ObjRef modeM (ObjName "B")) []
  pure (tt, aTy, bTy)

mkTransportTypeTheory :: IO (TypeTheory, Obj, Obj, Obj)
mkTransportTypeTheory = do
  env <- require (parseRawFile transportBuiltinSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "TransportBuiltin" env
  tt <- require (doctrineTypeTheory doc)
  let natOwner = ModeName "I"
  let natTy = mkCon (ObjRef natOwner (ObjName "Nat")) []
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  let zExpr = TMHead (GenName "Z") [] []
  let sExpr tm = TMHead (GenName "S") [THATm tm] []
  let addExpr lhs rhs = TMHead (GenName "add") [THATm lhs, THATm rhs] []
  let ssExpr = sExpr (sExpr zExpr)
  ssTm <- require (termExprToDiagram tt [] natTy ssExpr)
  add22Tm <- require (termExprToDiagram tt [] natTy (addExpr (sExpr zExpr) (sExpr zExpr)))
  let vecTy tm = mkCon (ObjRef modeM (ObjName "Vec")) [CATm tm, CAObj aTy]
  let vecAdd22 = vecTy add22Tm
  let vecSS2 = vecTy ssTm
  pure (tt, aTy, vecAdd22, vecSS2)

mkFoldBuiltinTypeTheory :: IO (TypeTheory, Obj, Obj)
mkFoldBuiltinTypeTheory = do
  env <- require (parseRawFile foldBuiltinSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "FoldBuiltin" env
  tt <- require (doctrineTypeTheory doc)
  let natTy = mkCon (ObjRef modeM (ObjName "Nat")) []
  let listTy = mkCon (ObjRef modeM (ObjName "List")) []
  pure (tt, natTy, listTy)

mkCtorElimBuiltinTypeTheory :: IO (TypeTheory, Obj, Obj, Obj, Obj, Obj)
mkCtorElimBuiltinTypeTheory = do
  env <- require (parseRawFile ctorElimBuiltinSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "CtorElimBuiltin" env
  tt <- require (doctrineTypeTheory doc)
  let natTy = mkCon (ObjRef modeI (ObjName "Nat")) []
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  let extraTy = mkCon (ObjRef modeM (ObjName "Extra")) []
  let outTy = mkCon (ObjRef modeM (ObjName "Out")) []
  let zExpr = TMHead (GenName "Z") [] []
  let sExpr tm = TMHead (GenName "S") [THATm tm] []
  ssTm <- require (termExprToDiagram tt [] natTy (sExpr (sExpr zExpr)))
  let vecTy tm = mkCon (ObjRef modeM (ObjName "Vec")) [CATm tm, CAObj aTy]
  pure (tt, aTy, extraTy, outTy, natTy, vecTy ssTm)

mkBinderTmCtxElimTypeTheory :: IO (ModuleEnv, Doctrine, TypeTheory, Obj)
mkBinderTmCtxElimTypeTheory = do
  env <- require (parseRawFile binderTmCtxElimSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "BinderTmCtxElim" env
  tt <- require (doctrineTypeTheory doc)
  let outTy = mkCon (ObjRef modeM (ObjName "Out")) []
  pure (env, doc, tt, outTy)

mkExplicitBuiltinElimTypeTheory :: IO (TypeTheory, Obj, Obj)
mkExplicitBuiltinElimTypeTheory = do
  doc <- require mkExplicitBuiltinElimDoctrine
  tt <- require (doctrineTypeTheory doc)
  let natTy = mkCon (ObjRef modeI (ObjName "Nat")) []
  let outTy = mkCon (ObjRef modeM (ObjName "Out")) []
  pure (tt, natTy, outTy)

mkHoleOrderedCtorElimTypeTheory :: IO (TypeTheory, Obj)
mkHoleOrderedCtorElimTypeTheory = do
  env <- require (parseRawFile holeOrderedCtorElimSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "HoleOrderedCtorElim" env
  tt <- require (doctrineTypeTheory doc)
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  pure (tt, aTy)

mkExplicitBuiltinElimDoctrine :: Either Text Doctrine
mkExplicitBuiltinElimDoctrine = do
  let uMTy = mkCon (ObjRef modeM (ObjName "U_M")) []
      uITy = mkCon (ObjRef modeI (ObjName "U_I")) []
      natTy = mkCon (ObjRef modeI (ObjName "Nat")) []
      outTy = mkCon (ObjRef modeM (ObjName "Out")) []
      bagTy = mkCon (ObjRef modeM (ObjName "Bag")) []
      natParam name =
        GP_Tm
          TmVar
            { tmvName = name
            , tmvSort = natTy
            , tmvScope = 0
            , tmvOwnerMode = Just modeI
            }
      mkGen mode name params dom cod =
        GenDecl
          { gdName = GenName name
          , gdMode = mode
          , gdParams = params
          , gdDom = dom
          , gdCod = cod
          , gdLiteralKind = Nothing
          }
      nilSlot = BinderSig { bsTmCtx = [natTy], bsDom = [], bsCod = [outTy] }
      consSlot = BinderSig { bsTmCtx = [natTy], bsDom = [], bsCod = [outTy] }
  mt0 <- addMode modeM emptyModeTheory
  mt1 <- addMode modeI mt0
  mt2 <-
    addClassification
      modeM
      ClassificationDecl
        { cdClassifier = modeM
        , cdUniverse = uMTy
        , cdComp = Nothing
        }
      mt1
  mt <-
    addClassification
      modeI
      ClassificationDecl
        { cdClassifier = modeI
        , cdUniverse = uITy
        , cdComp = Nothing
        }
      mt2
  let modeMGens =
        [ mkGen modeM "U_M" [] [] [uMTy]
        , mkGen modeM "Out" [] [] [uMTy]
        , mkGen modeM "Bag" [] [] [uMTy]
        , mkGen modeM "KeepNat" [natParam "n"] [] [outTy]
        , mkGen modeM "Nil" [] [] [bagTy]
        , mkGen modeM "Cons" [natParam "k"] [] [bagTy]
        , mkGen modeM "foldBag" [natParam "k"] [InPort bagTy, InBinder nilSlot, InBinder consSlot] [outTy]
        ]
      modeIGens =
        [ mkGen modeI "U_I" [] [] [uITy]
        , mkGen modeI "Nat" [] [] [uITy]
        , mkGen modeI "seed0" [] [] [natTy]
        , mkGen modeI "seed1" [] [] [natTy]
        ]
      builtins =
        [ BuiltinDecl
            { bdHead = GenName "foldBag"
            , bdMode = modeM
            , bdSpec =
                BDInductiveElim
                  0
                  [ BuiltinBranchDecl
                      { bbdCtor = GenName "Nil"
                      , bbdTmCtxInputs = [BISOuterHeadTmParam 0]
                      , bbdInputs = []
                      }
                  , BuiltinBranchDecl
                      { bbdCtor = GenName "Cons"
                      , bbdTmCtxInputs = [BISCtorHeadTmParam 0]
                      , bbdInputs = []
                      }
                  ]
            }
        ]
  pure
    Doctrine
      { dName = "ExplicitBuiltinElim"
      , dModes = mt
      , dAcyclicModes = S.empty
      , dGens =
          M.fromList
            [ (modeM, M.fromList [(gdName gd, gd) | gd <- modeMGens])
            , (modeI, M.fromList [(gdName gd, gd) | gd <- modeIGens])
            ]
      , dCells2 = []
      , dBuiltins = builtins
      , dActions = M.empty
      , dObligations = []
      }

mkLamIdBody :: Obj -> Either Text Diagram
mkLamIdBody aTy = do
  let (x, d0) = freshPort aTy (emptyDiagram modeM [])
  let body = d0 { dIn = [x], dOut = [x] }
  validateDiagram body
  pure body

mkConstBinderBody :: Obj -> GenName -> Either Text Diagram
mkConstBinderBody sortTy g = do
  tm <- mkConstClosedTerm modeM sortTy g
  pure (unTerm tm)

mkDropConstBody :: Obj -> Obj -> GenName -> Either Text Diagram
mkDropConstBody dropTy codTy g = do
  let (argIn, d0) = freshPort dropTy (emptyDiagram modeM [])
  let (out, d1) = freshPort codTy d0
  d2 <- addEdgePayload PInternalDrop [argIn] [] d1
  d3 <- addEdgePayload (PGen g [] []) [] [out] d2
  let diag = d3 { dIn = [argIn], dOut = [out] }
  validateDiagram diag
  pure diag

mkSuccTailBody :: Obj -> Either Text Diagram
mkSuccTailBody natTy = do
  let (headIn, d0) = freshPort natTy (emptyDiagram modeM [])
  let (tailIn, d1) = freshPort natTy d0
  let (out, d2) = freshPort natTy d1
  d3 <- addEdgePayload PInternalDrop [headIn] [] d2
  d4 <- addEdgePayload (PGen (GenName "Succ") [] []) [tailIn] [out] d3
  let diag = d4 { dIn = [headIn, tailIn], dOut = [out] }
  validateDiagram diag
  pure diag

mkUnaryBody :: Obj -> GenName -> Either Text Diagram
mkUnaryBody codTy g = do
  let (argIn, d0) = freshPort codTy (emptyDiagram modeM [])
  let (out, d2) = freshPort codTy d0
  d3 <- addEdgePayload (PGen g [] []) [argIn] [out] d2
  let diag = d3 { dIn = [argIn], dOut = [out] }
  validateDiagram diag
  pure diag

mkLocalTmParamBody :: TypeTheory -> Obj -> Obj -> GenName -> [Obj] -> Either Text Diagram
mkLocalTmParamBody tt localTmSort codTy headName domSorts = do
  localTm <- termExprToDiagram tt [localTmSort] localTmSort (TMBound 0)
  let allocInputs [] acc diag = Right (reverse acc, diag)
      allocInputs (ty : rest) acc diag = do
        let (pid, diag') = freshPort ty diag
        allocInputs rest (pid : acc) diag'
      dropInputs [] diag = Right diag
      dropInputs (pid : rest) diag = do
        diag' <- addEdgePayload PInternalDrop [pid] [] diag
        dropInputs rest diag'
  (ins, d0) <- allocInputs domSorts [] (emptyDiagram modeM [localTmSort])
  d1 <- dropInputs ins d0
  let (out, d2) = freshPort codTy d1
  d3 <- addEdgePayload (PGen headName [CATm localTm] []) [] [out] d2
  let diag = d3 { dIn = ins, dOut = [out] }
  validateDiagram diag
  pure diag

mkBetaInput :: Obj -> Either Text TermDiagram
mkBetaInput aTy = do
  body <- mkLamIdBody aTy
  let aToA = arrTy aTy aTy
  let headArgs = [CAObj aTy, CAObj aTy]
  let (x, d0) = freshPort aTy (emptyDiagram modeM [])
  let (lamOut, d1) = freshPort aToA d0
  let (y, d2) = freshPort aTy d1
  d3 <- addEdgePayload (PGen (GenName "lam") headArgs [BAConcrete body]) [] [lamOut] d2
  d4 <- addEdgePayload (PGen (GenName "app") headArgs []) [lamOut, x] [y] d3
  let diag = d4 { dIn = [x], dOut = [y] }
  validateDiagram diag
  pure (TermDiagram diag)

mkBetaWrapInput :: Obj -> Either Text TermDiagram
mkBetaWrapInput aTy = do
  body <- mkLamIdBody aTy
  let aToA = arrTy aTy aTy
  let headArgs = [CAObj aTy, CAObj aTy]
  let (x, d0) = freshPort aTy (emptyDiagram modeM [])
  let (lamOut, d1) = freshPort aToA d0
  let (mid, d2) = freshPort aTy d1
  let (out, d3) = freshPort aTy d2
  d4 <- addEdgePayload (PGen (GenName "lam") headArgs [BAConcrete body]) [] [lamOut] d3
  d5 <- addEdgePayload (PGen (GenName "app") headArgs []) [lamOut, x] [mid] d4
  d6 <- addEdgePayload (PGen (GenName "wrap") [CAObj aTy] []) [mid] [out] d5
  let diag = d6 { dIn = [x], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkRewriteLamInput :: Obj -> Either Text TermDiagram
mkRewriteLamInput aTy = do
  let aToA = arrTy aTy aTy
  let headArgs = [CAObj aTy, CAObj aTy]
  let (x, d0) = freshPort aTy (emptyDiagram modeM [])
  let (mkOut, d1) = freshPort aToA d0
  let (out, d2) = freshPort aTy d1
  d3 <- addEdgePayload (PGen (GenName "mkid") [CAObj aTy] []) [] [mkOut] d2
  d4 <- addEdgePayload (PGen (GenName "app") headArgs []) [mkOut, x] [out] d3
  let diag = d4 { dIn = [x], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkPackForceInput :: Obj -> Obj -> Either Text TermDiagram
mkPackForceInput aTy tagTy = do
  let (xBody, b0) = freshPort aTy (emptyDiagram modeM [])
  let (tagBody, b1) = freshPort tagTy b0
  b2 <- addEdgePayload PInternalDrop [tagBody] [] b1
  let body = b2 { dIn = [xBody, tagBody], dOut = [xBody] }
  validateDiagram body
  let cellTy = mkCon (ObjRef modeM (ObjName "Cell")) [CAObj aTy, CAObj aTy, CAObj tagTy]
  let headArgs = [CAObj aTy, CAObj aTy, CAObj tagTy]
  let (x, d0) = freshPort aTy (emptyDiagram modeM [])
  let (tagIn, d1) = freshPort tagTy d0
  let (packOut, d2) = freshPort cellTy d1
  let (out, d3) = freshPort aTy d2
  d4 <- addEdgePayload (PGen (GenName "pack") headArgs [BAConcrete body]) [] [packOut] d3
  d5 <- addEdgePayload (PGen (GenName "force") headArgs []) [packOut, x, tagIn] [out] d4
  let diag = d5 { dIn = [x, tagIn], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkIllTypedWrapInput :: Obj -> Either Text TermDiagram
mkIllTypedWrapInput aTy = do
  let aToA = arrTy aTy aTy
  let (x, d0) = freshPort aToA (emptyDiagram modeM [aToA])
  let (out, d1) = freshPort aTy d0
  d2 <- addEdgePayload (PGen (GenName "wrap") [CAObj aTy] []) [x] [out] d1
  let diag = d2 { dIn = [x], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkOpaqueBinderInput :: Obj -> Either Text TermDiagram
mkOpaqueBinderInput aTy = do
  body <- mkLamIdBody aTy
  let (out, d0) = freshPort aTy (emptyDiagram modeM [])
  d1 <- addEdgePayload (PGen (GenName "scope") [CAObj aTy] [BAConcrete body]) [] [out] d0
  let diag = d1 { dIn = [], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkNullaryHeadInput :: GenName -> [CodeArg] -> Obj -> Either Text TermDiagram
mkNullaryHeadInput g args sortTy = do
  let (out, d0) = freshPort sortTy (emptyDiagram modeM [])
  d1 <- addEdgePayload (PGen g args []) [] [out] d0
  let diag = d1 { dIn = [], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

applyUnaryHeadTerm :: GenName -> [CodeArg] -> Obj -> TermDiagram -> Either Text TermDiagram
applyUnaryHeadTerm g args sortTy (TermDiagram seed) = do
  validateDiagram seed
  inPid <-
    case dOut seed of
      [pid] -> Right pid
      _ -> Left "expected unary-head seed term to expose exactly one output"
  let (out, d0) = freshPort sortTy seed
  d1 <- addEdgePayload (PGen g args []) [inPid] [out] d0
  let diag = d1 { dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkMalformedBinderHeadInput :: Obj -> Either Text TermDiagram
mkMalformedBinderHeadInput aTy = do
  let (out, d0) = freshPort aTy (emptyDiagram modeM [])
  d1 <- addEdgePayload (PGen (GenName "scope") [CAObj aTy] []) [] [out] d0
  let diag = d1 { dIn = [], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkNestedInput :: Obj -> Either Text TermDiagram
mkNestedInput aTy = do
  let aToA = arrTy aTy aTy
  let aToAToA = arrTy aTy aToA
  let headArgsA = [CAObj aTy, CAObj aTy]
  let headArgsAtoA = [CAObj aTy, CAObj aToA]

  let (yPort, c0) = freshPort aTy (emptyDiagram modeM [])
  let (xPort, c1) = freshPort aTy c0
  c2 <- addEdgePayload PInternalDrop [yPort] [] c1
  let body2 = c2 { dIn = [yPort, xPort], dOut = [xPort] }
  validateDiagram body2

  let (xOuter, b0) = freshPort aTy (emptyDiagram modeM [])
  let (lam2Out, b1) = freshPort aToA b0
  b2 <- addEdgePayload (PGen (GenName "lam") headArgsA [BAConcrete body2]) [] [lam2Out] b1
  b3 <- addEdgePayload PInternalDrop [xOuter] [] b2
  let body1 = b3 { dIn = [xOuter], dOut = [lam2Out] }
  validateDiagram body1

  let (t1, d0) = freshPort aTy (emptyDiagram modeM [])
  let (t2, d1) = freshPort aTy d0
  let (lam1Out, d2) = freshPort aToAToA d1
  let (mid, d3) = freshPort aToA d2
  let (out, d4) = freshPort aTy d3
  d5 <- addEdgePayload (PGen (GenName "lam") headArgsAtoA [BAConcrete body1]) [] [lam1Out] d4
  d6 <- addEdgePayload (PGen (GenName "app") headArgsAtoA []) [lam1Out, t1] [mid] d5
  d7 <- addEdgePayload (PGen (GenName "app") headArgsA []) [mid, t2] [out] d6
  let diag = d7 { dIn = [t1, t2], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

testModeDeclInstallsFunctionBuiltins :: Assertion
testModeDeclInstallsFunctionBuiltins = do
  (tt, _aTy, _bTy) <- mkNbeTypeTheory
  case functionBuiltinForMode tt modeM of
    Just fb -> do
      fbLamGen fb @?= GenName "lam"
      fbAppGen fb @?= GenName "app"
      fbArrTyCon fb @?= ObjName "Arr"
    Nothing ->
      assertFailure "expected function-space builtins for NbE mode"

testBuiltinTransportEliminator :: Assertion
testBuiltinTransportEliminator = do
  (tt, aTy, vecAdd22, vecSS2) <- mkTransportTypeTheory
  extensionalBuiltinForMode tt modeM (GenName "expect22") @?= Just BuiltinTransport
  let mk22Expr = TMHead (GenName "mk22") [THAObj aTy] []

  canonicalSeed <- require (mkNullaryHeadInput (GenName "mk22") [CAObj aTy] vecSS2)
  canonicalTm <- require (applyUnaryHeadTerm (GenName "expect22") [CAObj aTy] vecSS2 canonicalSeed)
  canonicalNorm <- require (normalizeTermDiagram tt [] vecSS2 canonicalTm)
  canonicalExpr <- require (diagramToTermExpr tt [] vecSS2 canonicalNorm)
  canonicalExpr @?= mk22Expr

  let metaV =
        TmVar
          { tmvName = "w"
          , tmvSort = vecAdd22
          , tmvScope = 0
          , tmvOwnerMode = Just modeM
          }
  let (metaOut, meta0) = freshPort vecAdd22 (emptyDiagram modeM [])
  meta1 <- require (addEdgePayload (PTmMeta metaV) [] [metaOut] meta0)
  let neutralSeed = TermDiagram (meta1 { dIn = [], dOut = [metaOut] })
  neutralTm <- require (applyUnaryHeadTerm (GenName "expect22") [CAObj aTy] vecSS2 neutralSeed)
  neutralNorm <- require (normalizeTermDiagram tt [] vecSS2 neutralTm)
  neutralExpr <- require (diagramToTermExpr tt [] vecSS2 neutralNorm)
  case neutralExpr of
    TMMeta v [] -> tmvName v @?= "w"
    _ -> assertFailure ("expected builtin transport on neutral input to erase to the underlying meta, got: " <> show neutralExpr)

testCheckedBuiltinTransportConversion :: Assertion
testCheckedBuiltinTransportConversion = do
  (tt, aTy, _vecAdd22, vecSS2) <- mkTransportTypeTheory
  let expr =
        TMHead
          (GenName "expect22")
          [ THAObj aTy
          , THATm (TMHead (GenName "mk22") [THAObj aTy] [])
          ]
          []
  tm <- require (termExprToDiagramChecked tt [] vecSS2 expr)
  expr' <- require (diagramToTermExprChecked tt [] vecSS2 tm)
  expr' @?= expr

testBuiltinFoldEliminator :: Assertion
testBuiltinFoldEliminator = do
  (tt, natTy, _listTy) <- mkFoldBuiltinTypeTheory
  case eliminatorBuiltinForMode tt modeM (GenName "fold_List") of
    Just (BuiltinInductiveElim foldBuiltin) -> do
      iebScrutineeIndex foldBuiltin @?= 0
      map ebbCtorGen (iebBranches foldBuiltin) @?= [GenName "Nil", GenName "Cons"]
    other ->
      assertFailure ("expected fold_List to infer as a builtin constructor eliminator, got: " <> show other)
  nilBody <- require (mkConstBinderBody natTy (GenName "Zero"))
  consBody <- require (mkSuccTailBody natTy)
  let zeroExpr = TMHead (GenName "Zero") [] []
  let succExpr tm = TMHead (GenName "Succ") [THATm tm] []
  let nilExpr = TMHead (GenName "Nil") [] []
  let consExpr x xs = TMHead (GenName "Cons") [THATm x, THATm xs] []
  let listExpr = consExpr zeroExpr (consExpr (succExpr zeroExpr) nilExpr)
  let foldExpr =
        TMHead
          (GenName "fold_List")
          [ THAObj natTy
          , THATm listExpr
          ]
          [ TBABody nilBody
          , TBABody consBody
          ]
  tm <- require (termExprToDiagram tt [] natTy foldExpr)
  norm <- require (normalizeTermDiagram tt [] natTy tm)
  expr <- require (diagramToTermExpr tt [] natTy norm)
  expr @?= succExpr (succExpr zeroExpr)

testBuiltinFoldNeutralResidual :: Assertion
testBuiltinFoldNeutralResidual = do
  (tt, natTy, listTy) <- mkFoldBuiltinTypeTheory
  nilBody <- require (mkConstBinderBody natTy (GenName "Zero"))
  consBody <- require (mkSuccTailBody natTy)
  let expr =
        TMHead
          (GenName "fold_List")
          [ THAObj natTy
          , THATm (TMBound 0)
          ]
          [ TBABody nilBody
          , TBABody consBody
          ]
  tm <- require (termExprToDiagram tt [listTy] natTy expr)
  norm <- require (normalizeTermDiagram tt [listTy] natTy tm)
  expr' <- require (diagramToTermExpr tt [listTy] natTy norm)
  case expr' of
    TMHead g [THAObj natTy', THATm (TMBound 0)] bargs -> do
      g @?= GenName "fold_List"
      natTy' @?= natTy
      length bargs @?= 2
    _ ->
      assertFailure ("expected residual fold_List application on the boundary variable, got: " <> show expr')
  ok <- require (diagramIsoEq (unTerm norm) (unTerm tm))
  assertBool "expected fold on a neutral scrutinee to residualize without changing the term diagram" ok

testCtorElimTermParamsAndScrutineeIndex :: Assertion
testCtorElimTermParamsAndScrutineeIndex = do
  (tt, aTy, extraTy, outTy, _natTy, _vec2Ty) <- mkCtorElimBuiltinTypeTheory
  case eliminatorBuiltinForMode tt modeM (GenName "foldVec") of
    Just (BuiltinInductiveElim elimBuiltin) -> do
      iebScrutineeIndex elimBuiltin @?= 1
      map ebbCtorGen (iebBranches elimBuiltin) @?= [GenName "VNil", GenName "VCons"]
      map ebbTmCtxInputs (iebBranches elimBuiltin) @?= [[], []]
      map ebbInputs (iebBranches elimBuiltin) @?= [[BISOuterInput 0], [BISRecursiveResult 1 [RHCtorArg 0, RHCtorArg 1]]]
    other ->
      assertFailure ("expected foldVec to infer as a builtin constructor eliminator, got: " <> show other)
  nilBody <- require (mkDropConstBody extraTy outTy (GenName "ZeroOut"))
  consBody <- require (mkUnaryBody outTy (GenName "SuccOut"))
  let zExpr = TMHead (GenName "Z") [] []
  let sExpr tm = TMHead (GenName "S") [THATm tm] []
  let extraExpr = TMHead (GenName "e0") [] []
  let a0Expr = TMHead (GenName "a0") [] []
  let a1Expr = TMHead (GenName "a1") [] []
  let zeroOutExpr = TMHead (GenName "ZeroOut") [] []
  let succOutExpr tm = TMHead (GenName "SuccOut") [THATm tm] []
  let nilExpr = TMHead (GenName "VNil") [THAObj aTy] []
  let consExpr n x xs =
        TMHead
          (GenName "VCons")
          [ THATm n
          , THAObj aTy
          , THATm x
          , THATm xs
          ]
          []
  let vecExpr = consExpr (sExpr zExpr) a0Expr (consExpr zExpr a1Expr nilExpr)
  let foldExpr =
        TMHead
          (GenName "foldVec")
          [ THATm (sExpr (sExpr zExpr))
          , THAObj aTy
          , THATm extraExpr
          , THATm vecExpr
          ]
          [ TBABody nilBody
          , TBABody consBody
          ]
  tm <- require (termExprToDiagram tt [] outTy foldExpr)
  norm <- require (normalizeTermDiagram tt [] outTy tm)
  expr <- require (diagramToTermExpr tt [] outTy norm)
  expr @?= succOutExpr (succOutExpr zeroOutExpr)

testCtorElimBinderTmCtxFromOuterHead :: Assertion
testCtorElimBinderTmCtxFromOuterHead = do
  (env, doc, tt, outTy) <- mkBinderTmCtxElimTypeTheory
  case eliminatorBuiltinForMode tt modeM (GenName "run") of
    Just (BuiltinInductiveElim elimBuiltin) -> do
      iebScrutineeIndex elimBuiltin @?= 0
      map ebbCtorGen (iebBranches elimBuiltin) @?= [GenName "MkZeroBox"]
      map ebbTmCtxInputs (iebBranches elimBuiltin) @?= [[BISOuterHeadTmParam 0]]
      map ebbInputs (iebBranches elimBuiltin) @?= [[]]
    other ->
      assertFailure ("expected run to infer as a builtin constructor eliminator, got: " <> show other)
  raw <- require (parseDiagExpr "MkZeroBox ; run(S(Z))[Ignore(m)]")
  diag <- require (elabDiagExpr env doc modeM [] raw)
  norm <- require (normalizeTermDiagram tt [] outTy (TermDiagram diag))
  expr <- require (diagramToTermExpr tt [] outTy norm)
  let zExpr = TMHead (GenName "Z") [] []
      sExpr tm = TMHead (GenName "S") [THATm tm] []
  expr @?= TMHead (GenName "Ignore") [THATm (sExpr zExpr)] []

testCtorElimDependentBinderTmCtx :: Assertion
testCtorElimDependentBinderTmCtx = do
  (_env, _doc, tt, _outTy) <- mkBinderTmCtxElimTypeTheory
  let zExpr = TMHead (GenName "Z") [] []
      sExpr tm = TMHead (GenName "S") [THATm tm] []
      oneExpr = sExpr zExpr
      natTy = mkCon (ObjRef modeI (ObjName "Nat")) []
  boundTm <- require (termExprToDiagram tt [natTy] natTy (TMBound 0))
  oneTm <- require (termExprToDiagram tt [] natTy oneExpr)
  let boxOf tm = mkCon (ObjRef modeM (ObjName "Box")) [CATm tm]
  ctx <-
    require
      ( instantiateHostBoundCtx
          tt
          (structuralConvEnv tt)
          [natTy]
          (M.singleton 0 oneTm)
          [natTy, boxOf boundTm]
      )
  ctx @?= [natTy, boxOf oneTm]

testExplicitBuiltinSurfaceDecls :: Assertion
testExplicitBuiltinSurfaceDecls = do
  env <- require (parseRawFile explicitBuiltinSurfaceSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "ExplicitBuiltinSurface" env
  tt <- require (doctrineTypeTheory doc)
  case eliminatorBuiltinForMode tt modeM (GenName "choose") of
    Just (BuiltinInductiveElim elimBuiltin) -> do
      iebScrutineeIndex elimBuiltin @?= 0
      map ebbCtorGen (iebBranches elimBuiltin) @?= [GenName "K", GenName "C"]
      map ebbTmCtxInputs (iebBranches elimBuiltin) @?= [[], []]
      map ebbInputs (iebBranches elimBuiltin) @?= [[], []]
    other ->
      assertFailure ("expected choose to use the explicit builtin eliminator declaration, got: " <> show other)

testExplicitBuiltinSurfaceRejectsSortMismatch :: Assertion
testExplicitBuiltinSurfaceRejectsSortMismatch = do
  case parseRawFile explicitBuiltinBadSortSrc >>= elabRawFile of
    Left err ->
      assertBool
        ("expected builtin branch sort mismatch error, got: " <> T.unpack err)
        ("source sort mismatch" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected malformed explicit builtin declaration to be rejected during doctrine build"

testExplicitBuiltinElimSameSortBinderSource :: Assertion
testExplicitBuiltinElimSameSortBinderSource = do
  (tt, natTy, outTy) <- mkExplicitBuiltinElimTypeTheory
  case eliminatorBuiltinForMode tt modeM (GenName "foldBag") of
    Just (BuiltinInductiveElim elimBuiltin) -> do
      iebScrutineeIndex elimBuiltin @?= 0
      map ebbCtorGen (iebBranches elimBuiltin) @?= [GenName "Nil", GenName "Cons"]
      map ebbTmCtxInputs (iebBranches elimBuiltin) @?= [[BISOuterHeadTmParam 0], [BISCtorHeadTmParam 0]]
      map ebbInputs (iebBranches elimBuiltin) @?= [[], []]
    other ->
      assertFailure ("expected foldBag to use the explicit builtin eliminator metadata, got: " <> show other)
  nilBody <- require (mkLocalTmParamBody tt natTy outTy (GenName "KeepNat") [])
  consBody <- require (mkLocalTmParamBody tt natTy outTy (GenName "KeepNat") [])
  let seed0Expr = TMHead (GenName "seed0") [] []
      seed1Expr = TMHead (GenName "seed1") [] []
      consExpr x = TMHead (GenName "Cons") [THATm x] []
      keepExpr tm = TMHead (GenName "KeepNat") [THATm tm] []
      foldExpr =
        TMHead
          (GenName "foldBag")
          [ THATm seed0Expr
          , THATm (consExpr seed1Expr)
          ]
          [ TBABody nilBody
          , TBABody consBody
          ]
  tm <- require (termExprToDiagram tt [] outTy foldExpr)
  norm <- require (normalizeTermDiagram tt [] outTy tm)
  expr <- require (diagramToTermExpr tt [] outTy norm)
  expr @?= keepExpr seed1Expr

testInferredBuiltinElimUsesSpliceHoleIdentity :: Assertion
testInferredBuiltinElimUsesSpliceHoleIdentity = do
  (tt, aTy) <- mkHoleOrderedCtorElimTypeTheory
  case eliminatorBuiltinForMode tt modeM (GenName "choose") of
    Just (BuiltinInductiveElim elimBuiltin) -> do
      iebScrutineeIndex elimBuiltin @?= 0
      map ebbCtorGen (iebBranches elimBuiltin) @?= [GenName "K", GenName "C"]
      map ebbTmCtxInputs (iebBranches elimBuiltin) @?= [[], []]
      map ebbInputs (iebBranches elimBuiltin) @?= [[], []]
    other ->
      assertFailure ("expected choose to infer a builtin eliminator ordered by splice-hole identity, got: " <> show other)
  let kExpr = TMHead (GenName "K") [] []
      cExpr = TMHead (GenName "C") [] []
      kBodyExpr = TMHead (GenName "PickK") [] []
      cBodyExpr = TMHead (GenName "PickC") [] []
  kBody <- require (termExprToDiagram tt [] aTy kBodyExpr)
  cBody <- require (termExprToDiagram tt [] aTy cBodyExpr)
  let chooseExpr scrut =
        TMHead
          (GenName "choose")
          [THATm scrut]
          [ TBABody (unTerm kBody)
          , TBABody (unTerm cBody)
          ]
  chooseKTm <- require (termExprToDiagram tt [] aTy (chooseExpr kExpr))
  chooseCTm <- require (termExprToDiagram tt [] aTy (chooseExpr cExpr))
  chooseKNorm <- require (normalizeTermDiagram tt [] aTy chooseKTm)
  chooseCNorm <- require (normalizeTermDiagram tt [] aTy chooseCTm)
  chooseKExpr <- require (diagramToTermExpr tt [] aTy chooseKNorm)
  chooseCExpr <- require (diagramToTermExpr tt [] aTy chooseCNorm)
  chooseKExpr @?= kBodyExpr
  chooseCExpr @?= cBodyExpr

testInferredBuiltinElimRejectsConflictingHoleEvidence :: Assertion
testInferredBuiltinElimRejectsConflictingHoleEvidence =
  case parseRawFile conflictingHoleOrderedCtorElimSrc >>= elabRawFile of
    Left err ->
      assertBool
        ("expected conflicting builtin eliminator splice-hole evidence error, got: " <> T.unpack err)
        (  "conflicting rhs splice-hole evidence" `T.isInfixOf` err
        && "explicit `builtin eliminator ...` declaration" `T.isInfixOf` err
        )
    Right _ ->
      assertFailure "expected conflicting inferred builtin eliminator evidence to be rejected"

testCtorElimNonzeroScrutineeResidual :: Assertion
testCtorElimNonzeroScrutineeResidual = do
  (tt, aTy, extraTy, outTy, natTy, vec2Ty) <- mkCtorElimBuiltinTypeTheory
  nilBody <- require (mkDropConstBody extraTy outTy (GenName "ZeroOut"))
  consBody <- require (mkUnaryBody outTy (GenName "SuccOut"))
  let zExpr = TMHead (GenName "Z") [] []
  let sExpr tm = TMHead (GenName "S") [THATm tm] []
  let extraExpr = TMHead (GenName "e0") [] []
  let expr =
        TMHead
          (GenName "foldVec")
          [ THATm (sExpr (sExpr zExpr))
          , THAObj aTy
          , THATm extraExpr
          , THATm (TMBound 0)
          ]
          [ TBABody nilBody
          , TBABody consBody
          ]
  tm <- require (termExprToDiagram tt [vec2Ty] outTy expr)
  norm <- require (normalizeTermDiagram tt [vec2Ty] outTy tm)
  expr' <- require (diagramToTermExpr tt [vec2Ty] outTy norm)
  case expr' of
    TMHead g [THATm nExpr, THAObj aTy', THATm extraExpr', THATm (TMBound 0)] bargs -> do
      g @?= GenName "foldVec"
      aTy' @?= aTy
      nExpr @?= sExpr (sExpr zExpr)
      extraExpr' @?= extraExpr
      length bargs @?= 2
    _ ->
      assertFailure ("expected residual foldVec application on the boundary variable, got: " <> show expr')
  let sExprTm tmExpr = termExprToDiagram tt [] natTy tmExpr
  ssTm <- require (sExprTm (sExpr (sExpr zExpr)))
  mkCon (ObjRef modeM (ObjName "Vec")) [CATm ssTm, CAObj aTy] @?= vec2Ty
  ok <- require (diagramIsoEq (unTerm norm) (unTerm tm))
  assertBool "expected nonzero-scrutinee eliminator on a neutral input to residualize unchanged" ok

testNBEBeta :: Assertion
testNBEBeta = do
  (tt, aTy, _bTy) <- mkNbeTypeTheory
  tm <- require (mkBetaInput aTy)
  norm <- require (normalizeTermDiagram tt [aTy] aTy tm)
  let want = idDTm modeM [aTy] [aTy]
  ok <- require (diagramIsoEq (unTerm norm) want)
  assertBool "expected beta normal form to be the input variable" ok

testNBEEta :: Assertion
testNBEEta = do
  (tt, aTy, bTy) <- mkNbeTypeTheory
  let aToB = arrTy aTy bTy
  let tm = TermDiagram (idDTm modeM [aToB] [aToB])
  norm <- require (normalizeTermDiagram tt [aToB] aToB tm)
  let normDiag = unTerm norm
  let topEdges = IM.elems (dEdges normDiag)
  let lamBodies =
        [ (args, body)
        | Edge _ (PGen g args [BAConcrete body]) _ _ <- topEdges
        , g == GenName "lam"
        ]
  assertBool "expected exactly one top-level lam in eta normal form" (length lamBodies == 1)
  assertBool "expected top-level eta normal form to drop unused outer function input" (any isDrop topEdges)
  case lamBodies of
    [(lamArgs, body)] -> do
      lamArgs @?= [CAObj aTy, CAObj bTy]
      let bodyEdges = IM.elems (dEdges body)
      assertBool "expected lambda body to contain parameterized app node" (any (isApp aTy bTy) bodyEdges)
    _ ->
      pure ()
  where
    isDrop edge =
      case ePayload edge of
        PInternalDrop -> True
        _ -> False

    isApp aTy bTy edge =
      case ePayload edge of
        PGen g args [] -> g == GenName "app" && args == [CAObj aTy, CAObj bTy]
        _ -> False

testNBENestedBinders :: Assertion
testNBENestedBinders = do
  (tt, aTy, _bTy) <- mkNbeTypeTheory
  tm <- require (mkNestedInput aTy)
  norm <- require (normalizeTermDiagram tt [aTy, aTy] aTy tm)
  let normDiag = unTerm norm
  case (dIn normDiag, dOut normDiag) of
    (in0:in1:[], [out0]) -> do
      out0 @?= in0
      let dropped =
            [ ()
            | Edge _ PInternalDrop [pid] [] <- IM.elems (dEdges normDiag)
            , pid == in1
            ]
      assertBool "expected second boundary input to be dropped after nested beta" (length dropped == 1)
    _ ->
      assertFailure ("unexpected normalized boundary shape: " <> show normDiag)

testMixedBuiltinAndRewrite :: Assertion
testMixedBuiltinAndRewrite = do
  env <- require (parseRawFile mixedBuiltinRewriteSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "MixedBuiltinRewrite" env
  tt <- require (doctrineTypeTheory doc)
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  tm <- require (mkBetaWrapInput aTy)
  norm <- require (normalizeTermDiagram tt [aTy] aTy tm)
  let want = idDTm modeM [aTy] [aTy]
  ok <- require (diagramIsoEq (unTerm norm) want)
  assertBool
    ( "expected unified defeq to beta-reduce and then fire trusted rewrite rule, got: "
        <> show (unTerm norm)
    )
    ok

testResidualHeadSortMismatchRejected :: Assertion
testResidualHeadSortMismatchRejected = do
  env <- require (parseRawFile mixedBuiltinRewriteSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "MixedBuiltinRewrite" env
  tt <- require (doctrineTypeTheory doc)
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  let aToA = arrTy aTy aTy
  tm <- require (mkIllTypedWrapInput aTy)
  case diagramToTermExpr tt [aToA] aTy tm of
    Left err ->
      assertBool
        ("expected diagramToTermExpr to reject the malformed residual head, got: " <> T.unpack err)
        ("boundary input sort mismatch" `T.isInfixOf` err)
    Right expr ->
      assertFailure ("expected diagramToTermExpr to fail, got: " <> show expr)
  case normalizeTermDiagram tt [aToA] aTy tm of
    Left err ->
      assertBool
        ("expected NbE validation to reject the malformed residual head, got: " <> T.unpack err)
        ("NbE: boundary sort mismatch" `T.isInfixOf` err)
    Right norm ->
      assertFailure ("expected normalizeTermDiagram to fail, got: " <> show (unTerm norm))

testBinderHeadSignatureAndArity :: Assertion
testBinderHeadSignatureAndArity = do
  env <- require (parseRawFile binderResidualSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "BinderResidual" env
  tt <- require (doctrineTypeTheory doc)
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  case lookupTmHeadSig tt modeM (GenName "scope") of
    Just sig ->
      length (thsBinders sig) @?= 1
    Nothing ->
      assertFailure "expected binder-bearing head to be present in the unified head table"
  tm <- require (mkMalformedBinderHeadInput aTy)
  case normalizeTermDiagram tt [] aTy tm of
    Left err ->
      assertBool
        ("expected malformed binder arity to be rejected, got: " <> T.unpack err)
        ("residual head arity mismatch" `T.isInfixOf` err)
    Right norm ->
      assertFailure ("expected malformed binder head to fail, got: " <> show (unTerm norm))

testOpaqueBinderResidual :: Assertion
testOpaqueBinderResidual = do
  env <- require (parseRawFile binderResidualSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "BinderResidual" env
  tt <- require (doctrineTypeTheory doc)
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  tm <- require (mkOpaqueBinderInput aTy)
  norm <- require (normalizeTermDiagram tt [] aTy tm)
  ok <- require (diagramIsoEq (unTerm norm) (unTerm tm))
  assertBool
    ( "expected opaque binder residual to survive normalization, got: "
        <> show (unTerm norm)
    )
    ok

testBinderTermExprRoundtrip :: Assertion
testBinderTermExprRoundtrip = do
  env <- require (parseRawFile binderResidualSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "BinderResidual" env
  tt <- require (doctrineTypeTheory doc)
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  body <- require (mkLamIdBody aTy)
  let expr = TMHead (GenName "scope") [THAObj aTy] [TBABody body]
  tm <- require (termExprToDiagram tt [] aTy expr)
  expr' <- require (diagramToTermExpr tt [] aTy tm)
  expr' @?= expr

testBinderRewriteRules :: Assertion
testBinderRewriteRules = do
  env <- require (parseRawFile binderRewriteSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "BinderRewrite" env
  tt <- require (doctrineTypeTheory doc)
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  tm <- require (mkNullaryHeadInput (GenName "wrap") [CAObj aTy] aTy)
  norm <- require (normalizeTermDiagram tt [] aTy tm)
  want <- require (mkNullaryHeadInput (GenName "erase") [CAObj aTy] aTy)
  ok <- require (diagramIsoEq (unTerm norm) (unTerm want))
  assertBool
    ( "expected binder-bearing trusted rewrites to reduce wrap(A) to erase(A), got: "
        <> show (unTerm norm)
    )
    ok

testRewriteProducesBuiltinLambda :: Assertion
testRewriteProducesBuiltinLambda = do
  env <- require (parseRawFile rewriteBuiltinLamSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "RewriteBuiltinLam" env
  tt <- require (doctrineTypeTheory doc)
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  tm <- require (mkRewriteLamInput aTy)
  norm <- require (normalizeTermDiagram tt [aTy] aTy tm)
  let want = idDTm modeM [aTy] [aTy]
  ok <- require (diagramIsoEq (unTerm norm) want)
  assertBool
    ( "expected trusted rewrite RHS lambda to beta-reduce under app, got: "
        <> show (unTerm norm)
    )
    ok

testTrustedBinderSpliceRewrite :: Assertion
testTrustedBinderSpliceRewrite = do
  env <- require (parseRawFile trustedBinderSpliceSrc >>= elabRawFile)
  doc <- lookupDoctrineByName "TrustedBinderSplice" env
  tt <- require (doctrineTypeTheory doc)
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  let tagTy = mkCon (ObjRef modeM (ObjName "Tag")) []
  tm <- require (mkPackForceInput aTy tagTy)
  norm <- require (normalizeTermDiagram tt [aTy, tagTy] aTy tm)
  let normDiag = unTerm norm
  case (dTmCtx normDiag, dIn normDiag, dOut normDiag) of
    ([aTy', tagTy'], [x, tagIn], [out]) -> do
      aTy' @?= aTy
      tagTy' @?= tagTy
      out @?= x
      let drops =
            [ ()
            | Edge _ PInternalDrop [pid] [] <- IM.elems (dEdges normDiag)
            , pid == tagIn
            ]
      assertBool
        ( "expected trusted binder-hole beta rule to splice the captured body, got: "
            <> show normDiag
        )
        (length drops == 1)
    _ ->
      assertFailure
        ("unexpected normalized boundary shape for trusted binder splice rewrite: " <> show normDiag)

testTrustedModalSpliceRewrite :: Assertion
testTrustedModalSpliceRewrite = do
  let requireStage label = either (assertFailure . (\err -> label <> ": " <> T.unpack err)) pure
  doc <- requireStage "mk doctrine" mkTrustedModalSpliceDoctrine
  _ <- requireStage "validate doctrine" (validateDoctrine doc)
  tt <- requireStage "build type theory" (doctrineTypeTheory doc)
  let compiledRules = TRS.trsRules (compiledRulesForMode tt modeM)
      compiledMapped =
        [ rhs
        | rule <- compiledRules
        , Just rhs <- [TRS.trRHS rule]
        , termExprHasMappedSplice rhs
        ]
      rawMapped =
        [ rule
        | rule <- compiledRules
        , TRS.trRHS rule == Nothing
        , maybe False (diagramHasMappedSplice . unTerm) (TRS.trRHSDiagram rule)
        ]
  assertBool "expected mapped splice rule to compile to a term RHS" (not (null compiledMapped))
  assertBool ("expected no mapped-splice raw RHS fallback, got: " <> show (map TRS.trName rawMapped)) (null rawMapped)
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
  rawTm <- requireStage "parse input" (parseDiagExpr "(lam[(lam[id[A]] * id[A]) ; app] * id[A]) ; app")
  tm <- requireStage "elab input" (elabDiagExpr emptyEnv doc modeM [] rawTm)
  norm <- requireStage "normalize" (normalizeTermDiagramWithMapper tt (applyModExpr doc) [aTy] aTy (TermDiagram tm))
  expectedBody <- requireStage "expected binder body" (mkLamIdBodyFor modeM aTy)
  expr <- requireStage "quote normalized" (diagramToTermExpr tt [aTy] aTy norm)
  expr
    @?=
      TMHead
        (GenName "appB")
        [ THATm (TMHead (GenName "lamB") [] [TBABody expectedBody])
        , THATm (TMBound 0)
        ]
        []

termExprHasMappedSplice :: TermExpr -> Bool
termExprHasMappedSplice tm =
  case tm of
    TMBound _ -> False
    TMMeta _ _ -> False
    TMLit _ -> False
    TMHead _ args _ ->
      any headArgHasMappedSplice args
    TMSplice _ me args ->
      not (null (mePath me)) || any termExprHasMappedSplice args
  where
    headArgHasMappedSplice arg =
      case arg of
        THAObj _ -> False
        THATm inner -> termExprHasMappedSplice inner

diagramHasMappedSplice :: Diagram -> Bool
diagramHasMappedSplice =
  any edgeHasMappedSplice . IM.elems . dEdges
  where
    edgeHasMappedSplice edge =
      case ePayload edge of
        PSplice _ me -> not (null (mePath me))
        PGen _ args bargs ->
          any codeArgHasMappedSplice args || any binderArgHasMappedSplice bargs
        PBox _ inner -> diagramHasMappedSplice inner
        PFeedback inner -> diagramHasMappedSplice inner
        _ -> False

    codeArgHasMappedSplice arg =
      case arg of
        CAObj _ -> False
        CATm tm -> diagramHasMappedSplice (unTerm tm)

    binderArgHasMappedSplice barg =
      case barg of
        BAMeta _ -> False
        BAConcrete inner -> diagramHasMappedSplice inner

testActionSemanticsKernelFallback :: Assertion
testActionSemanticsKernelFallback = do
  doc <- require mkTrustedModalSpliceActionDoctrine
  tt <- require (doctrineTypeTheory doc)
  betaCell <-
    case [cell | cell <- dCells2 doc, c2Name cell == "beta_box"] of
      [cell] -> pure cell
      cells -> assertFailure ("expected exactly one beta_box cell, got " <> show (length cells)) >> fail "unreachable"
  lhs <- require (applyAction doc (ModName "Box") (c2LHS betaCell))
  rhs <- require (applyAction doc (ModName "Box") (c2RHS betaCell))
  direct <- require (defEqRuleTermDiagramWithMapper tt (applyModExpr doc) (dTmCtx lhs) (TermDiagram lhs) (TermDiagram rhs))
  assertBool
    ("expected direct kernel defeq on mapped rule sides, got lhs=" <> show lhs <> " rhs=" <> show rhs)
    direct
  result <- require (validateActionSemanticsWithBudgetResult defaultSearchBudget doc)
  case result of
    ActionSemanticsProved proofs ->
      assertBool
        ("expected kernel-defeq fallback witness for beta_box, got: " <> show proofs)
        (("rule beta_box", ASPKernelDefEq) `elem` proofs)
    ActionSemanticsUndecided label lim ->
      assertFailure ("expected action semantics proof, got undecided: " <> show (label, lim))

mkTrustedModalSpliceDoctrine :: Either Text Doctrine
mkTrustedModalSpliceDoctrine = do
  let boxMod = ModName "Box"
      boxExpr = ModExpr { meSrc = modeM, meTgt = modeM, mePath = [boxMod] }
      idExpr = ModExpr { meSrc = modeM, meTgt = modeM, mePath = [] }
      uTy = mkCon (ObjRef modeM (ObjName "U_M")) []
      boxUTy = OMod boxExpr uTy
      aTy = mkCon (ObjRef modeM (ObjName "A")) []
      lamBinder = BinderSig { bsTmCtx = [], bsDom = [aTy], bsCod = [aTy] }
      compDecl =
        CompDecl
          { compCtxExt = GenName "comp_ctx_ext"
          , compVar = GenName "comp_var"
          , compReindex = GenName "comp_reindex"
          }
      mkGen name dom cod =
        GenDecl
          { gdName = GenName name
          , gdMode = modeM
          , gdParams = []
          , gdDom = dom
          , gdCod = cod
          , gdLiteralKind = Nothing
          }
      gUM = mkGen "U_M" [] [boxUTy]
      gA = mkGen "A" [] [boxUTy]
      gCompCtxExt = mkGen "comp_ctx_ext" [InPort aTy] [aTy]
      gCompVar = mkGen "comp_var" [InPort aTy] [aTy]
      gCompReindex = mkGen "comp_reindex" [InPort aTy] [aTy]
      gLam = mkGen "lam" [InBinder lamBinder] [aTy]
      gApp = mkGen "app" [InPort aTy, InPort aTy] [aTy]
      gLamB = mkGen "lamB" [InBinder lamBinder] [aTy]
      gAppB = mkGen "appB" [InPort aTy, InPort aTy] [aTy]
      gens =
        [ gUM
        , gA
        , gCompCtxExt
        , gCompVar
        , gCompReindex
        , gLam
        , gApp
        , gLamB
        , gAppB
        ]
      gensByMode = M.singleton modeM (M.fromList [(gdName gd, gd) | gd <- gens])
  mt0 <- addMode modeM emptyModeTheory
  mt1 <- addModDecl ModDecl { mdName = boxMod, mdSrc = modeM, mdTgt = modeM } mt0
  mt2 <-
    addClassification
      modeM
      ClassificationDecl
        { cdClassifier = modeM
        , cdUniverse = boxUTy
        , cdComp = Just compDecl
        }
      mt1
  mt <- addClassifierLift boxMod idExpr mt2
  lamBImg <- genericGenDiagram gLamB
  appBImg <- genericGenDiagram gAppB
  let action =
        ModAction
          { maMod = boxMod
          , maGenMap =
              M.fromList
                [ ((modeM, gdName gLam), lamBImg)
                , ((modeM, gdName gApp), appBImg)
                ]
          , maPolicy = UseStructuralAsBidirectional
          }
      doc0 =
        Doctrine
          { dName = "TrustedModalSplice"
          , dModes = mt
          , dAcyclicModes = S.empty
          , dGens = gensByMode
          , dCells2 = []
          , dBuiltins = []
          , dActions = M.singleton boxMod action
          , dObligations = []
          }
  lhsRaw <- parseDiagExpr "(lam[?Body] * id[A]) ; app"
  (lhs, binderSigs) <- elabRuleLHS emptyEnv doc0 modeM [] [] lhsRaw
  rhsRaw <- parseDiagExpr "map[Box](splice(?Body))"
  rhs <- elabRuleRHS emptyEnv doc0 modeM [] [] binderSigs rhsRaw
  let betaCell =
        Cell2
          { c2Name = "beta_box"
          , c2Class = Computational
          , c2Orient = LR
          , c2Params = []
          , c2LHS = lhs
          , c2RHS = rhs
          }
  pure doc0 { dCells2 = [betaCell] }

mkTrustedModalSpliceActionDoctrine :: Either Text Doctrine
mkTrustedModalSpliceActionDoctrine = do
  doc0 <- mkTrustedModalSpliceDoctrine
  lhsRaw <- parseDiagExpr "(lamB[?Body] * id[A]) ; appB"
  (lhs, binderSigs) <- elabRuleLHS emptyEnv doc0 modeM [] [] lhsRaw
  rhsRaw <- parseDiagExpr "map[Box](map[Box](splice(?Body)))"
  rhs <- elabRuleRHS emptyEnv doc0 modeM [] [] binderSigs rhsRaw
  let mappedCell =
        Cell2
          { c2Name = "beta_box_mapped"
          , c2Class = Computational
          , c2Orient = LR
          , c2Params = []
          , c2LHS = lhs
          , c2RHS = rhs
          }
  pure doc0 { dCells2 = dCells2 doc0 <> [mappedCell] }

testDiagramBackedRewriteRHS :: Assertion
testDiagramBackedRewriteRHS = do
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
      xVar =
        TmVar
          { tmvName = "x"
          , tmvSort = aTy
          , tmvScope = 2
          , tmvOwnerMode = Nothing
          }
      yVar =
        TmVar
          { tmvName = "y"
          , tmvSort = aTy
          , tmvScope = 2
          , tmvOwnerMode = Nothing
          }
      pickName = GenName "pick"
      pickSig =
        TmHeadSig
          { thsParams = []
          , thsInputs = [aTy, aTy]
          , thsBinders = []
          , thsRes = aTy
          }
      baseTT =
        setModeTermHeads
          modeM
          (M.singleton pickName pickSig)
          (modeOnlyTypeTheory (mkModes [modeM]))
  rhsDiag <- TermDiagram <$> require (mkDiagramBackedPickRHS aTy xVar)
  let
      rule =
        TRS.TRule
          { TRS.trName = "pick_runtime_rhs"
          , TRS.trVars = [xVar, yVar]
          , TRS.trLHS = TMHead pickName [THATm (TMBound 0), THATm (TMBound 1)] []
          , TRS.trRHS = Nothing
          , TRS.trRHSDiagram = Just rhsDiag
          }
      tt = setModeCompiledRules modeM (TRS.mkTRS modeM [rule]) baseTT
      tmExpr = TMHead pickName [THATm (TMBound 0), THATm (TMBound 1)] []
  tm <- require (termExprToDiagram tt [aTy, aTy] aTy tmExpr)
  norm <- require (normalizeTermDiagram tt [aTy, aTy] aTy tm)
  expr <- require (diagramToTermExpr tt [aTy, aTy] aTy norm)
  expr @?= TMBound 0
  where
    mkDiagramBackedPickRHS aTy xVar =
      let (xIn, d0) = freshPort aTy (emptyDiagram modeM [aTy, aTy])
          (yIn, d1) = freshPort aTy d0
          (out, d2) = freshPort aTy d1
          (junkOut, d3) = freshPort aTy d2
          build = do
            d4 <- addEdgePayload (PTmMeta xVar) [xIn, yIn] [out] d3
            d5 <- addEdgePayload (PGen (GenName "junk") [] []) [] [junkOut] d4
            d6 <- addEdgePayload PInternalDrop [junkOut] [] d5
            let diag = d6 { dIn = [xIn, yIn], dOut = [out] }
            validateDiagram diag
            pure diag
       in build

testKernelStructuralToTermNormalization :: Assertion
testKernelStructuralToTermNormalization = do
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
      gName = GenName "g"
      gSig =
        TmHeadSig
          { thsParams = []
          , thsInputs = [aTy]
          , thsBinders = []
          , thsRes = aTy
          }
  gDiag <- require (mkUnaryHeadDiagram aTy gName)
  lhs <- require (mkBoxedTermDiagram aTy gDiag)
  let cell =
        Cell2
          { c2Name = "unwrap_box"
          , c2Class = Computational
          , c2Orient = LR
          , c2Params = []
          , c2LHS = lhs
          , c2RHS = gDiag
          }
      baseTT =
        setModeDiagramRules
          modeM
          [cell]
          ( setModeTermHeads
              modeM
              (M.singleton gName gSig)
              (modeOnlyTypeTheory (mkModes [modeM]))
          )
  tt <- require (withZeroParamGenArgSigs [c2LHS cell, c2RHS cell, lhs] baseTT)
  norm <- require (normalizeTermDiagram tt [aTy] aTy (TermDiagram lhs))
  expr <- require (diagramToTermExpr tt [aTy] aTy norm)
  expr @?= TMHead gName [THATm (TMBound 0)] []

testKernelStructuralResidualNormalization :: Assertion
testKernelStructuralResidualNormalization = do
  let aTy = mkCon (ObjRef modeM (ObjName "A")) []
      gName = GenName "g"
      gSig =
        TmHeadSig
          { thsParams = []
          , thsInputs = [aTy]
          , thsBinders = []
          , thsRes = aTy
          }
      idDiag = idDTm modeM [] [aTy]
  gDiag <- require (mkUnaryHeadDiagram aTy gName)
  host <- require (mkBoxedTermDiagram aTy gDiag)
  let cell =
        Cell2
          { c2Name = "rewrite_inside_box"
          , c2Class = Computational
          , c2Orient = LR
          , c2Params = []
          , c2LHS = gDiag
          , c2RHS = idDiag
          }
      baseTT =
        setModeDiagramRules
          modeM
          [cell]
          ( setModeTermHeads
              modeM
              (M.singleton gName gSig)
              (modeOnlyTypeTheory (mkModes [modeM]))
          )
  tt <- require (withZeroParamGenArgSigs [c2LHS cell, c2RHS cell, host] baseTT)
  norm <- require (normalizeTermDiagram tt [aTy] aTy (TermDiagram host))
  expected <- require (mkBoxedTermDiagram aTy idDiag)
  ok <- require (diagramIsoEq (unTerm norm) expected)
  assertBool
    ("expected kernel defeq to structurally normalize inside the box, got: " <> show (unTerm norm))
    ok

testBuiltinRewriteOverlapRejected :: Assertion
testBuiltinRewriteOverlapRejected =
  case parseRawFile builtinRewriteOverlapSrc >>= elabRawFile of
    Left err ->
      assertBool
        ("expected builtin/rule overlap rejection, got: " <> T.unpack err)
        (  "built-in computational heads may not also carry trusted user rewrite rules" `T.isInfixOf` err
        || "inferred builtin heads still have non-evidence trusted rules" `T.isInfixOf` err
        )
    Right _ ->
      assertFailure "expected doctrine elaboration to reject builtin-head rewrite overlap"

mkUnaryHeadDiagram :: Obj -> GenName -> Either Text Diagram
mkUnaryHeadDiagram aTy headName = do
  let (inPort, d0) = freshPort aTy (emptyDiagram modeM [])
  let (outPort, d1) = freshPort aTy d0
  d2 <- addEdgePayload (PGen headName [] []) [inPort] [outPort] d1
  let diag = d2 { dIn = [inPort], dOut = [outPort] }
  validateDiagram diag
  pure diag

mkBoxedTermDiagram :: Obj -> Diagram -> Either Text Diagram
mkBoxedTermDiagram aTy inner = do
  let inner' = inner { dTmCtx = [aTy] }
  let (inPort, d0) = freshPort aTy (emptyDiagram modeM [aTy])
  let (outPort, d1) = freshPort aTy d0
  d2 <- addEdgePayload (PBox (BoxName "KernelBox") inner') [inPort] [outPort] d1
  let diag = d2 { dIn = [inPort], dOut = [outPort] }
  validateDiagram diag
  pure diag

testNBEMissingLamRejected :: Assertion
testNBEMissingLamRejected =
  case parseRawFile nbeMissingLamSrc >>= elabRawFile of
    Left err ->
      assertBool
        ("expected missing-lam function-space builtin inference error, got: " <> T.unpack err)
        (  "incomplete function-space builtin evidence" `T.isInfixOf` err
        && "Arr" `T.isInfixOf` err
        )
    Right _ ->
      assertFailure "expected doctrine elaboration to reject incomplete function-space builtin evidence"

testNBEResidualizesSplice :: Assertion
testNBEResidualizesSplice = do
  (tt, aTy, _bTy) <- mkNbeTypeTheory
  let (x, d0) = freshPort aTy (emptyDiagram modeM [])
  let (y, d1) = freshPort aTy d0
  let me = ModExpr { meSrc = modeM, meTgt = modeM, mePath = [] }
  d2 <- require (addEdgePayload (PSplice (BinderMetaVar "b0") me) [x] [y] d1)
  let diag = d2 { dIn = [x], dOut = [y] }
  _ <- require (validateDiagram diag)
  let tm = TermDiagram diag
  norm <- require (normalizeTermDiagram tt [aTy] aTy tm)
  let normDiag = unTerm norm
  case (dTmCtx normDiag, dIn normDiag, dOut normDiag, IM.elems (dEdges normDiag)) of
    ([aTy'], [inp], [out], [Edge _ (PSplice hole me') [edgeIn] [edgeOut]]) -> do
      aTy' @?= aTy
      hole @?= BinderMetaVar "b0"
      me' @?= me
      edgeIn @?= inp
      edgeOut @?= out
    _ ->
      assertFailure
        ("expected NbE normalization to preserve unresolved splice structure, got: " <> show normDiag)

testMetaSpineNonPrefixStable :: Assertion
testMetaSpineNonPrefixStable = do
  (tt, aTy, _bTy) <- mkNbeTypeTheory
  let tmCtx = [aTy, aTy, aTy]
      mv =
        TmVar
          { tmvName = "m"
          , tmvSort = aTy
          , tmvScope = 2
          , tmvOwnerMode = Just modeM
          }
      tmExpr = TMMeta mv [0, 2]
  tm0 <- require (termExprToDiagram tt tmCtx aTy tmExpr)
  expr0 <- require (diagramToTermExpr tt tmCtx aTy tm0)
  expr0 @?= tmExpr
  norm <- require (normalizeTermDiagram tt tmCtx aTy tm0)
  exprNorm <- require (diagramToTermExpr tt tmCtx aTy norm)
  exprNorm @?= tmExpr
  tm1 <- require (termExprToDiagram tt tmCtx aTy exprNorm)
  ok <- require (diagramIsoEq (unTerm norm) (unTerm tm1))
  assertBool "expected meta-spine term->graph roundtrip stability after NbE" ok

testNeutralElimFrameResidual :: Assertion
testNeutralElimFrameResidual = do
  doc <- require (mkEligibilityDoctrine False)
  tt <- require (doctrineTypeTheory doc)
  case functionBuiltinForMode tt modeTy of
    Just fb ->
      assertBool "expected monomorphic function-space builtins to disable eta" (not (fbAllowEta fb))
    Nothing ->
      assertFailure "expected function-space builtins in constructor-eligibility doctrine"
  let natTy = mkCon (ObjRef modeTy (ObjName "Nat")) []
  let arrNatNat = mkCon (ObjRef modeTy (ObjName "Arr")) [CAObj natTy, CAObj natTy]
  tm <- require (mkNeutralAppInputMono arrNatNat natTy)
  norm <- require (normalizeTermDiagram tt [arrNatNat] natTy tm)
  expr <- require (diagramToTermExpr tt [arrNatNat] natTy norm)
  let want =
        TMHead
          (GenName "app")
          [ THATm (TMBound 0)
          , THATm (TMHead (GenName "z") [] [])
          ]
          []
  expr @?= want

testTRSStillChecked :: Assertion
testTRSStillChecked =
  case parseRawFile mixedNbeTrsSrc >>= elabRawFile of
    Left err ->
      assertBool
        ("expected TRS termination failure, got: " <> T.unpack err)
        (  "termination not proven" `T.isInfixOf` err
        && "ModeName \"I\"" `T.isInfixOf` err
        )
    Right _ ->
      assertFailure "expected doctrine elaboration to reject non-terminating TRS mode"

modeTy :: ModeName
modeTy = ModeName "Ty"

modeTm :: ModeName
modeTm = ModeName "Tm"

mkEligibilityModeTheory :: Obj -> Either Text ModeTheory
mkEligibilityModeTheory tmUniverse = do
  mt0 <- addMode modeTy emptyModeTheory
  mt1 <- addMode modeTm mt0
  let tyUniverse = mkCon (ObjRef modeTy (ObjName "U_Ty")) []
  mt2 <-
    addClassification
      modeTy
      ClassificationDecl
        { cdClassifier = modeTy
        , cdUniverse = tyUniverse
        
        , cdComp = Nothing
        }
      mt1
  addClassification
    modeTm
    ClassificationDecl
      { cdClassifier = modeTy
      , cdUniverse = tmUniverse
      
      , cdComp = Nothing
      }
    mt2

mkConstClosedTerm :: ModeName -> Obj -> GenName -> Either Text TermDiagram
mkConstClosedTerm mode sortTy g = do
  let (out, d0) = freshPort sortTy (emptyDiagram mode [])
  d1 <- addEdgePayload (PGen g [] []) [] [out] d0
  let diag = d1 { dIn = [], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkLamIdBodyFor :: ModeName -> Obj -> Either Text Diagram
mkLamIdBodyFor mode aTy = do
  let (x, d0) = freshPort aTy (emptyDiagram mode [])
  let body = d0 { dIn = [x], dOut = [x] }
  validateDiagram body
  pure body

mkClosedBetaTerm
  :: ModeName
  -> Obj
  -> Obj
  -> GenName
  -> GenName
  -> GenName
  -> Either Text TermDiagram
mkClosedBetaTerm mode natTy arrNatNat lamName appName zName = do
  body <- mkLamIdBodyFor mode natTy
  let (lamOut, d0) = freshPort arrNatNat (emptyDiagram mode [])
  let (zOut, d1) = freshPort natTy d0
  let (out, d2) = freshPort natTy d1
  d3 <- addEdgePayload (PGen lamName [] [BAConcrete body]) [] [lamOut] d2
  d4 <- addEdgePayload (PGen zName [] []) [] [zOut] d3
  d5 <- addEdgePayload (PGen appName [] []) [lamOut, zOut] [out] d4
  let diag = d5 { dIn = [], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkClosedSpliceTerm :: ModeName -> Obj -> GenName -> Either Text TermDiagram
mkClosedSpliceTerm mode sortTy seedGen = do
  let (mid, d0) = freshPort sortTy (emptyDiagram mode [])
  let (out, d1) = freshPort sortTy d0
  d2 <- addEdgePayload (PGen seedGen [] []) [] [mid] d1
  let me = ModExpr { meSrc = mode, meTgt = mode, mePath = [] }
  d3 <- addEdgePayload (PSplice (BinderMetaVar "s0") me) [mid] [out] d2
  let diag = d3 { dIn = [], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkNeutralAppInputMono :: Obj -> Obj -> Either Text TermDiagram
mkNeutralAppInputMono funTy argTy = do
  let (fIn, d0) = freshPort funTy (emptyDiagram modeTy [])
  let (zOut, d1) = freshPort argTy d0
  let (out, d2) = freshPort argTy d1
  d3 <- addEdgePayload (PGen (GenName "z") [] []) [] [zOut] d2
  d4 <- addEdgePayload (PGen (GenName "app") [] []) [fIn, zOut] [out] d3
  let diag = d4 { dIn = [fIn], dOut = [out] }
  validateDiagram diag
  pure (TermDiagram diag)

mkEligibilityDoctrine :: Bool -> Either Text Doctrine
mkEligibilityDoctrine includeBad = do
  let uTyRef = ObjRef modeTy (ObjName "U_Ty")
  let natRef = ObjRef modeTy (ObjName "Nat")
  let wrapRef = ObjRef modeTy (ObjName "Wrap")
  let arrRef = ObjRef modeTy (ObjName "Arr")
  let uTy = mkCon uTyRef []
  let natTy = mkCon natRef []
  let arrNatNat = mkCon arrRef [CAObj natTy, CAObj natTy]

  zTm <- mkConstClosedTerm modeTy natTy (GenName "z")
  betaTm <- mkClosedBetaTerm modeTy natTy arrNatNat (GenName "lam") (GenName "app") (GenName "z")
  badTm <- mkClosedSpliceTerm modeTy natTy (GenName "z")
  let tmUniverse = mkCon wrapRef [CATm zTm]
  mt <- mkEligibilityModeTheory tmUniverse

  let aTyVar = TmVar { tmvName = "a", tmvSort = uTy, tmvScope = 0, tmvOwnerMode = Just modeTy }
  let bTyVar = TmVar { tmvName = "b", tmvSort = uTy, tmvScope = 0, tmvOwnerMode = Just modeTy }
  let nTmVar = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 0, tmvOwnerMode = Just modeTy }

  let mkCtor name cod =
        GenDecl
          { gdName = GenName name
          , gdMode = modeTy
          , gdParams = []
          , gdDom = []
          , gdCod = [cod]
          , gdLiteralKind = Nothing
          }

  let gUTy = mkCtor "U_Ty" uTy
  let gNat = mkCtor "Nat" uTy
  let gZ = mkCtor "z" natTy
  let gBeta = mkCtor "Beta" (mkCon wrapRef [CATm betaTm])

  let gWrap =
        GenDecl
          { gdName = GenName "Wrap"
          , gdMode = modeTy
          , gdParams = [GP_Tm nTmVar]
          , gdDom = []
          , gdCod = [uTy]
          , gdLiteralKind = Nothing
          }

  let gArr =
        GenDecl
          { gdName = GenName "Arr"
          , gdMode = modeTy
          , gdParams = [GP_Ty aTyVar, GP_Ty bTyVar]
          , gdDom = []
          , gdCod = [uTy]
          , gdLiteralKind = Nothing
          }

  let lamBody = BinderSig { bsTmCtx = [], bsDom = [natTy], bsCod = [natTy] }
  let gLam =
        GenDecl
          { gdName = GenName "lam"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = [InBinder lamBody]
          , gdCod = [arrNatNat]
          , gdLiteralKind = Nothing
          }

  let gApp =
        GenDecl
          { gdName = GenName "app"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = [InPort arrNatNat, InPort natTy]
          , gdCod = [natTy]
          , gdLiteralKind = Nothing
          }

  let gBad =
        GenDecl
          { gdName = GenName "Bad"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = []
          , gdCod = [mkCon wrapRef [CATm badTm]]
          , gdLiteralKind = Nothing
          }

  let gens =
        [ gUTy
        , gNat
        , gWrap
        , gArr
        , gLam
        , gApp
        , gZ
        , gBeta
        ]
          <> [gBad | includeBad]
  pure
    Doctrine
      { dName = "CtorEligibilityNBE"
      , dModes = mt
      , dAcyclicModes = S.empty
            , dGens = M.fromList [(modeTy, M.fromList [(gdName gd, gd) | gd <- gens])]
      , dCells2 = []
      , dBuiltins = []
      , dActions = M.empty
      , dObligations = []
      }

mkMissingArrDoctrine :: Either Text Doctrine
mkMissingArrDoctrine = do
  mt0 <- addMode modeTy emptyModeTheory
  let uTy = mkCon (ObjRef modeTy (ObjName "U_Ty")) []
  mt <-
    addClassification
      modeTy
      ClassificationDecl
        { cdClassifier = modeTy
        , cdUniverse = uTy
        
        , cdComp = Nothing
        }
      mt0
  let natTy = mkCon (ObjRef modeTy (ObjName "Nat")) []
  let gUTy =
        GenDecl
          { gdName = GenName "U_Ty"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = []
          , gdCod = [uTy]
          , gdLiteralKind = Nothing
          }
  let gNat =
        GenDecl
          { gdName = GenName "Nat"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = []
          , gdCod = [uTy]
          , gdLiteralKind = Nothing
          }
  let arrNatNat = mkCon (ObjRef modeTy (ObjName "Arr")) [CAObj natTy, CAObj natTy]
  let lamBody = BinderSig { bsTmCtx = [], bsDom = [natTy], bsCod = [natTy] }
  let gLam =
        GenDecl
          { gdName = GenName "lam"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = [InBinder lamBody]
          , gdCod = [arrNatNat]
          , gdLiteralKind = Nothing
          }
  let gApp =
        GenDecl
          { gdName = GenName "app"
          , gdMode = modeTy
          , gdParams = []
          , gdDom = [InPort arrNatNat, InPort natTy]
          , gdCod = [natTy]
          , gdLiteralKind = Nothing
          }
  pure
    Doctrine
      { dName = "MissingArrInEligibility"
      , dModes = mt
      , dAcyclicModes = S.empty
            , dGens = M.fromList [(modeTy, M.fromList [(gdName gd, gd) | gd <- [gUTy, gNat, gLam, gApp]])]
      , dCells2 = []
      , dBuiltins = []
      , dActions = M.empty
      , dObligations = []
      }

testCtorEligibilityUsesNBE :: Assertion
testCtorEligibilityUsesNBE = do
  doc <- require (mkEligibilityDoctrine False)
  tables <- require (deriveCtorTables doc)
  let tmTable = M.findWithDefault M.empty modeTm tables
  assertBool "expected Beta constructor in Tm owner vocabulary under NbE eligibility" (M.member (ObjName "Beta") tmTable)

testCtorEligibilityDefEqExclusion :: Assertion
testCtorEligibilityDefEqExclusion = do
  doc <- require (mkEligibilityDoctrine True)
  tables <- require (deriveCtorTables doc)
  let tyTable = M.findWithDefault M.empty modeTy tables
  let tmTable = M.findWithDefault M.empty modeTm tables
  assertBool
    "expected non-defeq constructor Bad to stay out of Ty eligibility tables"
    (M.notMember (ObjName "Bad") tyTable)
  assertBool
    "expected non-defeq constructor Bad to stay out of Tm eligibility tables"
    (M.notMember (ObjName "Bad") tmTable)
  assertBool
    "expected valid constructor Beta to remain admitted in Tm eligibility tables"
    (M.member (ObjName "Beta") tmTable)

mkEligibilityDoctrineMalformedLam :: Either Text Doctrine
mkEligibilityDoctrineMalformedLam = do
  doc <- mkEligibilityDoctrine False
  modeGens <-
    case M.lookup modeTy (dGens doc) of
      Just gs -> Right gs
      Nothing -> Left "missing Ty mode generator table"
  lamDecl <-
    case M.lookup (GenName "lam") modeGens of
      Just gd -> Right gd
      Nothing -> Left "missing lam generator declaration"
  let lamDecl2 = lamDecl { gdName = GenName "lam2" }
  let modeGens' = M.insert (gdName lamDecl2) lamDecl2 modeGens
  pure doc { dGens = M.insert modeTy modeGens' (dGens doc) }

testCtorEligibilityLamShapeRejected :: Assertion
testCtorEligibilityLamShapeRejected = do
  doc <- require mkEligibilityDoctrineMalformedLam
  case deriveCtorTables doc of
    Left err ->
      assertBool
        ("expected ambiguous function-space builtin inference during ctor eligibility validation, got: " <> T.unpack err)
        ("ambiguous function-space builtin evidence" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected deriveCtorTables to reject malformed NbE lam config"

testCtorEligibilityMissingArrRejected :: Assertion
testCtorEligibilityMissingArrRejected = do
  doc <- require mkMissingArrDoctrine
  case doctrineTypeTheory doc of
    Left err ->
      assertBool
        ("expected missing Arr function-space builtin validation error, got: " <> T.unpack err)
        (  "missing function-space arrow type constructor" `T.isInfixOf` err
        && "Arr" `T.isInfixOf` err
        )
    Right _ ->
      assertFailure "expected doctrineTypeTheory to reject function-space builtins without Arr constructor"

testNBEOutputSortDefEq :: Assertion
testNBEOutputSortDefEq = do
  doc <- require (mkEligibilityDoctrine False)
  tt <- require (doctrineTypeTheory doc)
  let natTy = mkCon (ObjRef modeTy (ObjName "Nat")) []
  let arrNatNat = mkCon (ObjRef modeTy (ObjName "Arr")) [CAObj natTy, CAObj natTy]
  let wrapRef = ObjRef modeTy (ObjName "Wrap")
  zTm <- require (mkConstClosedTerm modeTy natTy (GenName "z"))
  betaTm <- require (mkClosedBetaTerm modeTy natTy arrNatNat (GenName "lam") (GenName "app") (GenName "z"))
  let expectedSort = mkCon wrapRef [CATm zTm]
  let metaSort = mkCon wrapRef [CATm betaTm]
  let v = TmVar { tmvName = "w", tmvSort = metaSort, tmvScope = 0, tmvOwnerMode = Just modeTy }
  let (out, d0) = freshPort metaSort (emptyDiagram modeTy [])
  d1 <- require (addEdgePayload (PTmMeta v) [] [out] d0)
  let diag = d1 { dIn = [], dOut = [out] }
  _ <- require (validateDiagram diag)
  _ <- require (normalizeTermDiagram tt [] expectedSort (TermDiagram diag))
  pure ()

testCATmObjectNormalization :: Assertion
testCATmObjectNormalization = do
  doc <- require (mkEligibilityDoctrine False)
  tt <- require (doctrineTypeTheory doc)
  let natTy = mkCon (ObjRef modeTy (ObjName "Nat")) []
  let arrNatNat = mkCon (ObjRef modeTy (ObjName "Arr")) [CAObj natTy, CAObj natTy]
  let wrapRef = ObjRef modeTy (ObjName "Wrap")
  zTm <- require (mkConstClosedTerm modeTy natTy (GenName "z"))
  betaTm <- require (mkClosedBetaTerm modeTy natTy arrNatNat (GenName "lam") (GenName "app") (GenName "z"))
  let src = mkCon wrapRef [CATm betaTm]
  let want = mkCon wrapRef [CATm zTm]
  got <- require (normalizeObjDeepWithCtx tt [] src)
  got @?= want

transportBuiltinSrc :: Text
transportBuiltinSrc =
  T.unlines
    [ "doctrine TransportBuiltin where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  mode I classifiedBy I via I.U_I;"
    , "  gen i_ctx_ext(a@I) : [a] -> [a] @I;"
    , "  gen i_var(a@I) : [a] -> [a] @I;"
    , "  gen i_reindex(a@I) : [a] -> [a] @I;"
    , "  comprehension I where { ctx_ext = i_ctx_ext; var = i_var; reindex = i_reindex; };"
    , "  gen U_I : [] -> [I.U_I] @I;"
    , "  gen Nat : [] -> [I.U_I] @I;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Vec(n : Nat, a@M) : [] -> [M.U_M] @M;"
    , "  gen Z : [] -> [Nat] @I;"
    , "  gen S : [Nat] -> [Nat] @I;"
    , "  gen add : [Nat, Nat] -> [Nat] @I;"
    , "  rule computational addZ -> : [Nat] -> [Nat] @I ="
    , "    (Z * id[Nat]) ; add == id[Nat]"
    , "  rule computational addS -> : [Nat, Nat] -> [Nat] @I ="
    , "    (S * id[Nat]) ; add == add ; S"
    , "  gen mk22(a@M) : [] -> [Vec(S(S(Z)), a)] @M;"
    , "  gen expect22(a@M) : [Vec(add(S(Z), S(Z)), a)] -> [Vec(S(S(Z)), a)] @M;"
    , "}"
    ]

foldBuiltinSrc :: Text
foldBuiltinSrc =
  T.unlines
    [ "doctrine FoldBuiltin where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  data Nat @M where {"
    , "    Zero : [];"
    , "    Succ : [Nat];"
    , "  }"
    , "  gen dropNat : [Nat] -> [] @M;"
    , "  data List @M where {"
    , "    Nil : [];"
    , "    Cons : [Nat, List];"
    , "  }"
    , "}"
    ]

ctorElimBuiltinSrc :: Text
ctorElimBuiltinSrc =
  T.unlines
    [ "doctrine CtorElimBuiltin where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  mode I classifiedBy I via I.U_I;"
    , "  gen i_ctx_ext(a@I) : [a] -> [a] @I;"
    , "  gen i_var(a@I) : [a] -> [a] @I;"
    , "  gen i_reindex(a@I) : [a] -> [a] @I;"
    , "  comprehension I where { ctx_ext = i_ctx_ext; var = i_var; reindex = i_reindex; };"
    , "  gen U_I : [] -> [I.U_I] @I;"
    , "  gen Nat : [] -> [I.U_I] @I;"
    , "  gen Z : [] -> [Nat] @I;"
    , "  gen S : [Nat] -> [Nat] @I;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Extra : [] -> [M.U_M] @M;"
    , "  gen Out : [] -> [M.U_M] @M;"
    , "  gen a0 : [] -> [A] @M;"
    , "  gen a1 : [] -> [A] @M;"
    , "  gen e0 : [] -> [Extra] @M;"
    , "  gen ZeroOut : [] -> [Out] @M;"
    , "  gen SuccOut : [Out] -> [Out] @M;"
    , "  gen drop(a@M) : [a] -> [] @M;"
    , "  gen dropA : [A] -> [] @M;"
    , "  gen dropExtra : [Extra] -> [] @M;"
    , "  gen swap(a@M, b@M) : [a, b] -> [b, a] @M;"
    , "  gen Vec(n : Nat, a@M) : [] -> [M.U_M] @M;"
    , "  gen VNil(a@M) : [] -> [Vec(Z, a)] @M;"
    , "  gen VCons(n : Nat, a@M) : [a, Vec(n, a)] -> [Vec(S(n), a)] @M;"
    , "  gen foldVec(n : Nat, a@M) :"
    , "    [Extra, Vec(n, a), binder { extra : Extra } : [Out], binder { acc : Out } : [Out]] -> [Out] @M;"
    , "  rule computational foldVec_nil -> (a@M) : [Extra] -> [Out] @M ="
    , "    (id[Extra] * VNil(a)) ; foldVec(Z, a)[?NilCase, ?ConsCase] == splice(?NilCase)"
    , "  rule computational foldVec_cons -> (n : Nat, a@M) : [Extra, a, Vec(n, a)] -> [Out] @M ="
    , "    (id[Extra] * VCons(n, a)) ; foldVec(S(n), a)[?NilCase, ?ConsCase]"
    , "      == (swap(Extra, a) * id[Vec(n, a)]) ; (id[a] * foldVec(n, a)[?NilCase, ?ConsCase]) ; (drop(a) * id[Out]) ; splice(?ConsCase)"
    , "}"
    ]

binderTmCtxElimSrc :: Text
binderTmCtxElimSrc =
  T.unlines
    [ "doctrine BinderTmCtxElim where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  mode I classifiedBy I via I.U_I;"
    , "  gen i_ctx_ext(a@I) : [a] -> [a] @I;"
    , "  gen i_var(a@I) : [a] -> [a] @I;"
    , "  gen i_reindex(a@I) : [a] -> [a] @I;"
    , "  comprehension I where { ctx_ext = i_ctx_ext; var = i_var; reindex = i_reindex; };"
    , "  gen U_I : [] -> [I.U_I] @I;"
    , "  gen Nat : [] -> [I.U_I] @I;"
    , "  gen Z : [] -> [Nat] @I;"
    , "  gen S : [Nat] -> [Nat] @I;"
    , "  gen Out : [] -> [M.U_M] @M;"
    , "  gen Ignore(n : Nat) : [] -> [Out] @M;"
    , "  gen Box(n : Nat) : [] -> [M.U_M] @M;"
    , "  gen MkZeroBox : [] -> [Box(Z)] @M;"
    , "  gen run(k : Nat) : [Box(Z), binder { tm m : Nat } : [Out]] -> [Out] @M;"
    , "  rule computational run_zero -> (k : Nat) : [] -> [Out] @M ="
    , "    MkZeroBox ; run(k)[?Case] == splice(?Case)"
    , "}"
    ]

explicitBuiltinSurfaceSrc :: Text
explicitBuiltinSurfaceSrc =
  T.unlines
    [ "doctrine ExplicitBuiltinSurface where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen D : [] -> [M.U_M] @M;"
    , "  gen K : [] -> [D] @M;"
    , "  gen C : [] -> [D] @M;"
    , "  gen choose : [D, binder { } : [A], binder { } : [A]] -> [A] @M;"
    , "  builtin eliminator choose @ M where {"
    , "    scrutinee = 0;"
    , "    branch K { inputs = []; };"
    , "    branch C { inputs = []; };"
    , "  }"
    , "}"
    ]

explicitBuiltinBadSortSrc :: Text
explicitBuiltinBadSortSrc =
  T.unlines
    [ "doctrine ExplicitBuiltinBadSort where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen D : [] -> [M.U_M] @M;"
    , "  gen K : [] -> [D] @M;"
    , "  gen C : [] -> [D] @M;"
    , "  gen choose : [D, binder { x : A } : [A], binder { y : A } : [A]] -> [A] @M;"
    , "  builtin eliminator choose @ M where {"
    , "    scrutinee = 0;"
    , "    branch K { inputs = [outer_input 0]; };"
    , "    branch C { inputs = [outer_input 0]; };"
    , "  }"
    , "}"
    ]

holeOrderedCtorElimSrc :: Text
holeOrderedCtorElimSrc =
  T.unlines
    [ "doctrine HoleOrderedCtorElim where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen D : [] -> [M.U_M] @M;"
    , "  gen K : [] -> [D] @M;"
    , "  gen C : [] -> [D] @M;"
    , "  gen PickK : [] -> [A] @M;"
    , "  gen PickC : [] -> [A] @M;"
    , "  gen choose : [D, binder { } : [A], binder { } : [A]] -> [A] @M;"
    , "  rule computational choose_c -> : [] -> [A] @M ="
    , "    C ; choose[?OnK, ?OnC] == splice(?OnC)"
    , "  rule computational choose_k -> : [] -> [A] @M ="
    , "    K ; choose[?OnK, ?OnC] == splice(?OnK)"
    , "}"
    ]

conflictingHoleOrderedCtorElimSrc :: Text
conflictingHoleOrderedCtorElimSrc =
  T.unlines
    [ "doctrine ConflictingHoleOrderedCtorElim where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen D : [] -> [M.U_M] @M;"
    , "  gen K : [] -> [D] @M;"
    , "  gen C : [] -> [D] @M;"
    , "  gen choose : [D, binder { } : [A], binder { } : [A]] -> [A] @M;"
    , "  rule computational choose_c -> : [] -> [A] @M ="
    , "    C ; choose[?OnK, ?OnC] == splice(?OnC)"
    , "  rule computational choose_k -> : [] -> [A] @M ="
    , "    K ; choose[?OnK, ?OnC] == splice(?OnC)"
    , "}"
    ]

nbeDoctrineSrc :: Text
nbeDoctrineSrc =
  T.unlines
    [ "doctrine NBEMode where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen B : [] -> [M.U_M] @M;"
    , "  gen Arr(a@M, b@M) : [] -> [M.U_M] @M;"
    , "  gen lam(a@M, b@M) : [binder { x : a } : [b]] -> [Arr(a, b)] @M;"
    , "  gen app(a@M, b@M) : [Arr(a, b), a] -> [b] @M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "}"
    ]

nbeMissingLamSrc :: Text
nbeMissingLamSrc =
  T.unlines
    [ "doctrine NBEMissingLam where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Arr(a@M, b@M) : [] -> [M.U_M] @M;"
    , "  gen app(a@M, b@M) : [Arr(a, b), a] -> [b] @M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "}"
    ]

mixedNbeTrsSrc :: Text
mixedNbeTrsSrc =
  T.unlines
    [ "doctrine MixedNbeTrs where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Arr(a@M, b@M) : [] -> [M.U_M] @M;"
    , "  gen lam(a@M, b@M) : [binder { x : a } : [b]] -> [Arr(a, b)] @M;"
    , "  gen app(a@M, b@M) : [Arr(a, b), a] -> [b] @M;"
    , "  gen m_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen m_var(a@M) : [a] -> [a] @M;"
    , "  gen m_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = m_ctx_ext; var = m_var; reindex = m_reindex; };"
    , ""
    , "  mode I classifiedBy I via I.U_I;"
    , "  gen i_ctx_ext(a@I) : [a] -> [a] @I;"
    , "  gen i_var(a@I) : [a] -> [a] @I;"
    , "  gen i_reindex(a@I) : [a] -> [a] @I;"
    , "  comprehension I where { ctx_ext = i_ctx_ext; var = i_var; reindex = i_reindex; };"
    , "  gen U_I : [] -> [I.U_I] @I;"
    , "  gen Nat : [] -> [I.U_I] @I;"
    , "  gen f : [Nat] -> [Nat] @I;"
    , "  rule computational loop -> : [Nat] -> [Nat] @I ="
    , "    id[Nat] ; f == id[Nat] ; f"
    , "}"
    ]

mixedBuiltinRewriteSrc :: Text
mixedBuiltinRewriteSrc =
  T.unlines
    [ "doctrine MixedBuiltinRewrite where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Arr(a@M, b@M) : [] -> [M.U_M] @M;"
    , "  gen lam(a@M, b@M) : [binder { x : a } : [b]] -> [Arr(a, b)] @M;"
    , "  gen app(a@M, b@M) : [Arr(a, b), a] -> [b] @M;"
    , "  gen wrap(a@M) : [a] -> [a] @M;"
    , "  rule computational wrap_id -> (a@M) : [a] -> [a] @M ="
    , "    id[a] ; wrap(a) == id[a]"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "}"
    ]

binderResidualSrc :: Text
binderResidualSrc =
  T.unlines
    [ "doctrine BinderResidual where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Arr(a@M, b@M) : [] -> [M.U_M] @M;"
    , "  gen lam(a@M, b@M) : [binder { x : a } : [b]] -> [Arr(a, b)] @M;"
    , "  gen app(a@M, b@M) : [Arr(a, b), a] -> [b] @M;"
    , "  gen scope(a@M) : [binder { x : a } : [a]] -> [a] @M;"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "}"
    ]

binderRewriteSrc :: Text
binderRewriteSrc =
  T.unlines
    [ "doctrine BinderRewrite where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Arr(a@M, b@M) : [] -> [M.U_M] @M;"
    , "  gen lam(a@M, b@M) : [binder { x : a } : [b]] -> [Arr(a, b)] @M;"
    , "  gen app(a@M, b@M) : [Arr(a, b), a] -> [b] @M;"
    , "  gen scope(a@M) : [binder { x : a } : [a]] -> [a] @M;"
    , "  gen wrap(a@M) : [] -> [a] @M;"
    , "  gen erase(a@M) : [] -> [a] @M;"
    , "  rule computational wrap_scope -> (a@M) : [] -> [a] @M ="
    , "    wrap(a) == scope(a)[id[a]]"
    , "  rule computational scope_erase -> (a@M) : [] -> [a] @M ="
    , "    scope(a)[id[a]] == erase(a)"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "}"
    ]

rewriteBuiltinLamSrc :: Text
rewriteBuiltinLamSrc =
  T.unlines
    [ "doctrine RewriteBuiltinLam where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Arr(a@M, b@M) : [] -> [M.U_M] @M;"
    , "  gen lam(a@M, b@M) : [binder { x : a } : [b]] -> [Arr(a, b)] @M;"
    , "  gen app(a@M, b@M) : [Arr(a, b), a] -> [b] @M;"
    , "  gen mkid(a@M) : [] -> [Arr(a, a)] @M;"
    , "  rule computational mkid_lam -> (a@M) : [] -> [Arr(a, a)] @M ="
    , "    mkid(a) == lam(a, a)[id[a]]"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "}"
    ]

trustedBinderSpliceSrc :: Text
trustedBinderSpliceSrc =
  T.unlines
    [ "doctrine TrustedBinderSplice where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Tag : [] -> [M.U_M] @M;"
    , "  gen Cell(a@M, b@M, t@M) : [] -> [M.U_M] @M;"
    , "  gen pack(a@M, b@M, t@M) : [binder { x : a, tag : t } : [b]] -> [Cell(a, b, t)] @M;"
    , "  gen force(a@M, b@M, t@M) : [Cell(a, b, t), a, t] -> [b] @M;"
    , "  rule computational beta -> (a@M, b@M, t@M) : [a, t] -> [b] @M ="
    , "    (pack(a, b, t)[?Body] * id[a] * id[t]) ; force(a, b, t) == splice(?Body)"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "}"
    ]

builtinRewriteOverlapSrc :: Text
builtinRewriteOverlapSrc =
  T.unlines
    [ "doctrine BuiltinRewriteOverlap where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen A : [] -> [M.U_M] @M;"
    , "  gen Arr(a@M, b@M) : [] -> [M.U_M] @M;"
    , "  gen lam(a@M, b@M) : [binder { x : a } : [b]] -> [Arr(a, b)] @M;"
    , "  gen app(a@M, b@M) : [Arr(a, b), a] -> [b] @M;"
    , "  rule computational bad_app -> (a@M, b@M) : [Arr(a, b), a] -> [b] @M ="
    , "    app(a, b) == app(a, b)"
    , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen comp_var(a@M) : [a] -> [a] @M;"
    , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
    , "}"
    ]
