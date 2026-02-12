{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Morphism
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.Common.Rules (RewritePolicy(..), RuleClass(..), Orientation(..))
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Poly.ModeTheory
import Strat.Poly.TypeExpr
import Strat.Poly.IndexTheory (IxTheory(..), IxFunSig(..))
import Strat.Poly.Names
import Strat.Poly.Diagram
import Strat.Poly.Graph (Edge(..), EdgePayload(..), BinderArg(..), BinderMetaVar(..), diagramIsoEq)
import Strat.Poly.Cell2
import Strat.Poly.Doctrine
import Strat.Poly.Morphism
import Strat.Poly.TypeTheory (modeOnlyTypeTheory)
import Test.Poly.Helpers (mkModes, identityModeMap, identityModMap)


tests :: TestTree
tests =
  testGroup
    "Poly.Morphism"
    [ testCase "monoid morphism to string monoid" testMonoidMorphism
    , testCase "type map can reorder parameters" testTypeMapReorder
    , testCase "cross-mode morphism applies mode map" testCrossModeMorphism
    , testCase "modality map rewrites modality applications in types" testModalityMapRewritesTypeModalities
    , testCase "morphism rejects index function maps with arity mismatch" testIxFunMapArityMismatch
    , testCase "morphism rejects index function maps with sort mismatch" testIxFunMapSortMismatch
    , testCase "morphism instantiation fails on dependent substitution errors" testMorphismInstantiationSubstFailure
    , testCase "binder generator identity morphism preserves binder arguments" testBinderIdentityMorphismPreservesBinders
    , testCase "morphism rewrites splice binder holes to substituted binder metas" testMorphismSpliceRenamesToBinderMeta
    , testCase "morphism checker rejects incorrect binder-hole signatures" testMorphismRejectsBadBinderHoleSignatures
    , testCase "morphism rejects cyclic type templates" testTypeTemplateCycleRejected
    , testCase "morphism rejects indexed template sort mismatch in same mode" testIndexedTemplateSortMismatch
    , testCase "morphism type map instantiates indexed templates" testIndexedTypeTemplateInstantiation
    , testCase "morphism rejects indexed template parameter kind mismatch" testIndexedTemplateKindMismatch
    , testCase "morphism check all enforces computational equations" testMorphismCheckAllEnforcesComputational
    , testCase "morphism check structural ignores computational equations" testMorphismCheckStructuralIgnoresComputational
    , testCase "morphism check none skips structural equations" testMorphismCheckNoneSkipsStructural
    , testCase "morphism elaboration rejects generator images with wrong boundaries" testMorphismRejectsBadGenImageBoundaryAtElab
    , testCase "wire metavariable rules elaborate" testWireMetaRuleElaborates
    , testCase "wire metavariables reject duplicate names in one diagram" testWireMetaRuleRejectsDuplicateName
    ]

tvar :: ModeName -> Text -> TyVar
tvar mode name = TyVar { tvName = name, tvMode = mode }

tcon :: ModeName -> Text -> [TypeExpr] -> TypeExpr
tcon mode name args = TCon (TypeRef mode (TypeName name)) (map TAType args)

plainImage :: Diagram -> GenImage
plainImage diag = GenImage diag M.empty

setSingleEdgeBargs :: Diagram -> [BinderArg] -> Either Text Diagram
setSingleEdgeBargs diag bargs =
  case IM.toList (dEdges diag) of
    [(edgeKey, edge@(Edge _ (PGen g attrs _) _ _))] ->
      let edge' = edge { ePayload = PGen g attrs bargs }
      in pure diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
    _ -> Left "expected a single generator edge"

setSingleEdgePayload :: Diagram -> EdgePayload -> Either Text Diagram
setSingleEdgePayload diag payload =
  case IM.toList (dEdges diag) of
    [(edgeKey, edge)] ->
      let edge' = edge { ePayload = payload }
      in pure diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
    _ -> Left "expected a single edge"

testMonoidMorphism :: Assertion
testMonoidMorphism = do
  docSrc <- either (assertFailure . T.unpack) pure mkMonoid
  docTgt <- either (assertFailure . T.unpack) pure mkStringMonoid
  let modeMap = identityModeMap docSrc
  let typeMap = M.fromList [(TypeRef modeM (TypeName "A"), TypeTemplate [] (tcon modeM "Str" []))]
  unitImg <- either (assertFailure . T.unpack) pure (genD modeM [] [tcon modeM "Str" []] (GenName "empty"))
  mulImg <- either (assertFailure . T.unpack) pure (genD modeM [tcon modeM "Str" [], tcon modeM "Str" []] [tcon modeM "Str" []] (GenName "append"))
  let mor = Morphism
        { morName = "MonoidToStr"
        , morSrc = docSrc
        , morTgt = docTgt
        , morIsCoercion = False
        , morModeMap = modeMap
        , morModMap = identityModMap docSrc
        , morAttrSortMap = M.empty
        , morTypeMap = typeMap
        , morGenMap = M.fromList [((modeM, GenName "unit"), plainImage unitImg), ((modeM, GenName "mul"), plainImage mulImg)]
        , morIxFunMap = M.empty
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        , morFuel = 20
        }
  case checkMorphism mor of
    Left err -> assertFailure (show err)
    Right () -> pure ()

testTypeMapReorder :: Assertion
testTypeMapReorder = do
  let mode = ModeName "M"
  let a = tvar mode "a"
  let b = tvar mode "b"
  let prod = TypeName "Prod"
  let pair = TypeName "Pair"
  let genName = GenName "g"
  let genSrc =
        GenDecl
          { gdName = genName
          , gdMode = mode
          , gdTyVars = [a, b]
          , gdIxVars = []
          , gdDom = map InPort [TCon (TypeRef mode prod) [TAType (TVar a), TAType (TVar b)]]
          , gdCod = [TCon (TypeRef mode prod) [TAType (TVar a), TAType (TVar b)]]
          , gdAttrs = []
          }
  let genTgt =
        GenDecl
          { gdName = genName
          , gdMode = mode
          , gdTyVars = [a, b]
          , gdIxVars = []
          , gdDom = map InPort [TCon (TypeRef mode pair) [TAType (TVar a), TAType (TVar b)]]
          , gdCod = [TCon (TypeRef mode pair) [TAType (TVar a), TAType (TVar b)]]
          , gdAttrs = []
          }
  let docSrc = Doctrine
        { dName = "Src"
        , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
      , dAttrSorts = M.empty
        , dTypes = M.fromList [(mode, M.fromList [(prod, TypeSig [PS_Ty mode, PS_Ty mode])])]
        , dGens = M.fromList [(mode, M.fromList [(genName, genSrc)])]
        , dCells2 = []
        }
  let docTgt = Doctrine
        { dName = "Tgt"
        , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
      , dAttrSorts = M.empty
        , dTypes = M.fromList [(mode, M.fromList [(pair, TypeSig [PS_Ty mode, PS_Ty mode])])]
        , dGens = M.fromList [(mode, M.fromList [(genName, genTgt)])]
        , dCells2 = []
        }
  docSrc' <- case validateDoctrine docSrc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docSrc
  docTgt' <- case validateDoctrine docTgt of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docTgt
  img <- either (assertFailure . T.unpack) pure (genD mode [TCon (TypeRef mode pair) [TAType (TVar b), TAType (TVar a)]] [TCon (TypeRef mode pair) [TAType (TVar b), TAType (TVar a)]] genName)
  let typeMap = M.fromList [(TypeRef mode prod, TypeTemplate [TPType a, TPType b] (TCon (TypeRef mode pair) [TAType (TVar b), TAType (TVar a)]))]
  let mor = Morphism
        { morName = "SwapProd"
        , morSrc = docSrc'
        , morTgt = docTgt'
        , morIsCoercion = False
        , morModeMap = identityModeMap docSrc'
        , morModMap = identityModMap docSrc'
        , morAttrSortMap = M.empty
        , morTypeMap = typeMap
        , morGenMap = M.fromList [((mode, genName), plainImage img)]
        , morIxFunMap = M.empty
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        , morFuel = 20
        }
  case checkMorphism mor of
    Left err -> assertFailure (show err)
    Right () -> pure ()

testCrossModeMorphism :: Assertion
testCrossModeMorphism = do
  let modeC = ModeName "C"
  let modeV = ModeName "V"
  let aRef = TypeRef modeC (TypeName "A")
  let bRef = TypeRef modeV (TypeName "B")
  let aTy = TCon aRef []
  let bTy = TCon bRef []
  let fGen =
        GenDecl
          { gdName = GenName "f"
          , gdMode = modeC
          , gdTyVars = []
          , gdIxVars = []
          , gdDom = map InPort [aTy]
          , gdCod = [aTy]
          , gdAttrs = []
          }
  let gGen =
        GenDecl
          { gdName = GenName "g"
          , gdMode = modeV
          , gdTyVars = []
          , gdIxVars = []
          , gdDom = map InPort [bTy]
          , gdCod = [bTy]
          , gdAttrs = []
          }
  let docSrc = Doctrine
        { dName = "Src"
        , dModes = mkModes [modeC]
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
      , dAttrSorts = M.empty
        , dTypes = M.fromList [(modeC, M.fromList [(TypeName "A", TypeSig [])])]
        , dGens = M.fromList [(modeC, M.fromList [(GenName "f", fGen)])]
        , dCells2 = []
        }
  let docTgt = Doctrine
        { dName = "Tgt"
        , dModes = mkModes [modeV]
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
      , dAttrSorts = M.empty
        , dTypes = M.fromList [(modeV, M.fromList [(TypeName "B", TypeSig [])])]
        , dGens = M.fromList [(modeV, M.fromList [(GenName "g", gGen)])]
        , dCells2 = []
        }
  docSrc' <- case validateDoctrine docSrc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docSrc
  docTgt' <- case validateDoctrine docTgt of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docTgt
  img <- either (assertFailure . T.unpack) pure (genD modeV [bTy] [bTy] (GenName "g"))
  let mor = Morphism
        { morName = "CtoV"
        , morSrc = docSrc'
        , morTgt = docTgt'
        , morIsCoercion = False
        , morModeMap = M.fromList [(modeC, modeV)]
        , morModMap = identityModMap docSrc'
        , morAttrSortMap = M.empty
        , morTypeMap = M.fromList [(aRef, TypeTemplate [] bTy)]
        , morGenMap = M.fromList [((modeC, GenName "f"), plainImage img)]
        , morIxFunMap = M.empty
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        , morFuel = 20
        }
  case checkMorphism mor of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  srcDiag <- either (assertFailure . T.unpack) pure (genD modeC [aTy] [aTy] (GenName "f"))
  tgtDiag <- either (assertFailure . T.unpack) pure (applyMorphismDiagram mor srcDiag)
  dMode tgtDiag @?= modeV
  dom <- either (assertFailure . T.unpack) pure (diagramDom tgtDiag)
  cod <- either (assertFailure . T.unpack) pure (diagramCod tgtDiag)
  dom @?= [bTy]
  cod @?= [bTy]

testModalityMapRewritesTypeModalities :: Assertion
testModalityMapRewritesTypeModalities = do
  let modeA = ModeName "A"
  let modeB = ModeName "B"
  let modeC = ModeName "C"
  let modeD = ModeName "D"
  let modF = ModName "F"
  let modH = ModName "H"
  let modG = ModName "G"
  let modK = ModName "K"
  let fSrc = ModExpr { meSrc = modeA, meTgt = modeB, mePath = [modF] }
  let hSrc = ModExpr { meSrc = modeB, meTgt = modeB, mePath = [modH] }
  let gTgt = ModExpr { meSrc = modeC, meTgt = modeD, mePath = [modG] }
  let kTgt = ModExpr { meSrc = modeD, meTgt = modeD, mePath = [modK] }
  let baseSrc = tcon modeA "Base" []
  let baseTgt = tcon modeC "Base" []
  let fBaseSrc = TMod fSrc baseSrc
  let hfBaseSrc = TMod hSrc fBaseSrc
  let gBaseTgt = TMod gTgt baseTgt
  let kgBaseTgt = TMod kTgt gBaseTgt
  let gkBaseTgt = TMod (ModExpr { meSrc = modeC, meTgt = modeD, mePath = [modG, modK] }) baseTgt
  let modeTheorySrc =
        ModeTheory
          { mtModes =
              M.fromList
                [ (modeA, ModeInfo modeA Linear)
                , (modeB, ModeInfo modeB Linear)
                ]
          , mtDecls =
              M.fromList
                [ (modF, ModDecl modF modeA modeB)
                , (modH, ModDecl modH modeB modeB)
                ]
          , mtEqns = []
          , mtAdjs = []
          }
  let modeTheoryTgt =
        ModeTheory
          { mtModes =
              M.fromList
                [ (modeC, ModeInfo modeC Linear)
                , (modeD, ModeInfo modeD Linear)
                ]
          , mtDecls =
              M.fromList
                [ (modG, ModDecl modG modeC modeD)
                , (modK, ModDecl modK modeD modeD)
                ]
          , mtEqns = []
          , mtAdjs = []
          }
  let genGSrc =
        GenDecl
          { gdName = GenName "g"
          , gdMode = modeB
          , gdTyVars = []
          , gdIxVars = []
          , gdDom = map InPort [fBaseSrc]
          , gdCod = [fBaseSrc]
          , gdAttrs = []
          }
  let genGGSrc =
        GenDecl
          { gdName = GenName "gg"
          , gdMode = modeB
          , gdTyVars = []
          , gdIxVars = []
          , gdDom = map InPort [hfBaseSrc]
          , gdCod = [hfBaseSrc]
          , gdAttrs = []
          }
  let genGTgt =
        GenDecl
          { gdName = GenName "g"
          , gdMode = modeD
          , gdTyVars = []
          , gdIxVars = []
          , gdDom = map InPort [gBaseTgt]
          , gdCod = [gBaseTgt]
          , gdAttrs = []
          }
  let genGGTgt =
        GenDecl
          { gdName = GenName "gg"
          , gdMode = modeD
          , gdTyVars = []
          , gdIxVars = []
          , gdDom = map InPort [kgBaseTgt]
          , gdCod = [kgBaseTgt]
          , gdAttrs = []
          }
  let docSrc = Doctrine
        { dName = "SrcModal"
        , dModes = modeTheorySrc
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
      , dAttrSorts = M.empty
        , dTypes = M.fromList [(modeA, M.fromList [(TypeName "Base", TypeSig [])])]
        , dGens = M.fromList [(modeB, M.fromList [(GenName "g", genGSrc), (GenName "gg", genGGSrc)])]
        , dCells2 = []
        }
  let docTgt = Doctrine
        { dName = "TgtModal"
        , dModes = modeTheoryTgt
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
      , dAttrSorts = M.empty
        , dTypes = M.fromList [(modeC, M.fromList [(TypeName "Base", TypeSig [])])]
        , dGens = M.fromList [(modeD, M.fromList [(GenName "g", genGTgt), (GenName "gg", genGGTgt)])]
        , dCells2 = []
        }
  docSrc' <- case validateDoctrine docSrc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docSrc
  docTgt' <- case validateDoctrine docTgt of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docTgt
  imgG <- either (assertFailure . T.unpack) pure (genD modeD [gBaseTgt] [gBaseTgt] (GenName "g"))
  imgGG <- either (assertFailure . T.unpack) pure (genD modeD [kgBaseTgt] [kgBaseTgt] (GenName "gg"))
  let mor = Morphism
        { morName = "ModalMap"
        , morSrc = docSrc'
        , morTgt = docTgt'
        , morIsCoercion = False
        , morModeMap = M.fromList [(modeA, modeC), (modeB, modeD)]
        , morModMap = M.fromList [(modF, gTgt), (modH, kTgt)]
        , morAttrSortMap = M.empty
        , morTypeMap = M.fromList [(TypeRef modeA (TypeName "Base"), TypeTemplate [] baseTgt)]
        , morGenMap = M.fromList [((modeB, GenName "g"), plainImage imgG), ((modeB, GenName "gg"), plainImage imgGG)]
        , morIxFunMap = M.empty
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        , morFuel = 20
        }
  case checkMorphism mor of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()

  srcDiagG <- either (assertFailure . T.unpack) pure (genD modeB [fBaseSrc] [fBaseSrc] (GenName "g"))
  tgtDiagG <- either (assertFailure . T.unpack) pure (applyMorphismDiagram mor srcDiagG)
  dMode tgtDiagG @?= modeD
  domG <- either (assertFailure . T.unpack) pure (diagramDom tgtDiagG)
  codG <- either (assertFailure . T.unpack) pure (diagramCod tgtDiagG)
  domG @?= [gBaseTgt]
  codG @?= [gBaseTgt]
  assertSingleGenEdge "g" tgtDiagG

  srcDiagGG <- either (assertFailure . T.unpack) pure (genD modeB [hfBaseSrc] [hfBaseSrc] (GenName "gg"))
  tgtDiagGG <- either (assertFailure . T.unpack) pure (applyMorphismDiagram mor srcDiagGG)
  dMode tgtDiagGG @?= modeD
  domGG <- either (assertFailure . T.unpack) pure (diagramDom tgtDiagGG)
  codGG <- either (assertFailure . T.unpack) pure (diagramCod tgtDiagGG)
  domGG @?= [gkBaseTgt]
  codGG @?= [gkBaseTgt]
  assertSingleGenEdge "gg" tgtDiagGG
  where
    assertSingleGenEdge name diag =
      case IM.elems (dEdges diag) of
        [Edge _ (PGen genName attrs bargs) _ _] -> do
          genName @?= GenName name
          attrs @?= M.empty
          bargs @?= []
        _ -> assertFailure "expected exactly one generator edge"

testIxFunMapArityMismatch :: Assertion
testIxFunMapArityMismatch = do
  let modeI = ModeName "I"
  let modeJ = ModeName "J"
  let natTy = TCon (TypeRef modeI (TypeName "Nat")) []
  let symTy = TCon (TypeRef modeJ (TypeName "Sym")) []
  let srcDoc =
        Doctrine
          { dName = "SrcIx"
          , dModes = mkModes [modeI, modeJ]
    , dAcyclicModes = S.empty
          , dIndexModes = S.fromList [modeI, modeJ]
          , dIxTheory =
              M.fromList
                [ ( modeI
                  , IxTheory
                      { itFuns = M.fromList [(IxFunName "Z", IxFunSig [] natTy)]
                      , itRules = []
                      }
                  )
                , ( modeJ
                  , IxTheory
                      { itFuns = M.fromList [(IxFunName "pair", IxFunSig [natTy, natTy] symTy)]
                      , itRules = []
                      }
                  )
                ]
          , dAttrSorts = M.empty
          , dTypes =
              M.fromList
                [ (modeI, M.fromList [(TypeName "Nat", TypeSig [])])
                , (modeJ, M.fromList [(TypeName "Sym", TypeSig [])])
                ]
          , dGens = M.empty
          , dCells2 = []
          }
  let tgtDoc =
        Doctrine
          { dName = "TgtIx"
          , dModes = mkModes [modeI, modeJ]
    , dAcyclicModes = S.empty
          , dIndexModes = S.fromList [modeI, modeJ]
          , dIxTheory =
              M.fromList
                [ ( modeI
                  , IxTheory
                      { itFuns = M.fromList [(IxFunName "Z", IxFunSig [] natTy)]
                      , itRules = []
                      }
                  )
                , ( modeJ
                  , IxTheory
                      { itFuns = M.fromList [(IxFunName "single", IxFunSig [natTy] symTy)]
                      , itRules = []
                      }
                  )
                ]
          , dAttrSorts = M.empty
          , dTypes =
              M.fromList
                [ (modeI, M.fromList [(TypeName "Nat", TypeSig [])])
                , (modeJ, M.fromList [(TypeName "Sym", TypeSig [])])
                ]
          , dGens = M.empty
          , dCells2 = []
          }
  src <- either (assertFailure . T.unpack) pure (validateDoctrine srcDoc >> Right srcDoc)
  tgt <- either (assertFailure . T.unpack) pure (validateDoctrine tgtDoc >> Right tgtDoc)
  let mor =
        Morphism
          { morName = "BadIxArity"
          , morSrc = src
          , morTgt = tgt
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morAttrSortMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morIxFunMap = M.fromList [(IxFunName "pair", IxFunName "single")]
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          , morFuel = 20
          }
  case checkMorphism mor of
    Left err -> assertBool "expected arity mismatch error" ("arity mismatch" `T.isInfixOf` err)
    Right () -> assertFailure "expected morphism check to fail"

testIxFunMapSortMismatch :: Assertion
testIxFunMapSortMismatch = do
  let modeI = ModeName "I"
  let modeJ = ModeName "J"
  let natTy = TCon (TypeRef modeI (TypeName "Nat")) []
  let boolTy = TCon (TypeRef modeI (TypeName "Bool")) []
  let symTy = TCon (TypeRef modeJ (TypeName "Sym")) []
  let srcDoc =
        Doctrine
          { dName = "SrcIxSort"
          , dModes = mkModes [modeI, modeJ]
    , dAcyclicModes = S.empty
          , dIndexModes = S.fromList [modeI, modeJ]
          , dIxTheory =
              M.fromList
                [ ( modeI
                  , IxTheory
                      { itFuns = M.fromList [(IxFunName "Z", IxFunSig [] natTy)]
                      , itRules = []
                      }
                  )
                , ( modeJ
                  , IxTheory
                      { itFuns = M.fromList [(IxFunName "f", IxFunSig [natTy] symTy)]
                      , itRules = []
                      }
                  )
                ]
          , dAttrSorts = M.empty
          , dTypes =
              M.fromList
                [ ( modeI
                  , M.fromList
                      [ (TypeName "Nat", TypeSig [])
                      , (TypeName "Bool", TypeSig [])
                      ]
                  )
                , (modeJ, M.fromList [(TypeName "Sym", TypeSig [])])
                ]
          , dGens = M.empty
          , dCells2 = []
          }
  let tgtDoc =
        Doctrine
          { dName = "TgtIxSort"
          , dModes = mkModes [modeI, modeJ]
    , dAcyclicModes = S.empty
          , dIndexModes = S.fromList [modeI, modeJ]
          , dIxTheory =
              M.fromList
                [ ( modeI
                  , IxTheory
                      { itFuns = M.fromList [(IxFunName "B0", IxFunSig [] boolTy)]
                      , itRules = []
                      }
                  )
                , ( modeJ
                  , IxTheory
                      { itFuns = M.fromList [(IxFunName "g", IxFunSig [boolTy] symTy)]
                      , itRules = []
                      }
                  )
                ]
          , dAttrSorts = M.empty
          , dTypes =
              M.fromList
                [ ( modeI
                  , M.fromList
                      [ (TypeName "Nat", TypeSig [])
                      , (TypeName "Bool", TypeSig [])
                      ]
                  )
                , (modeJ, M.fromList [(TypeName "Sym", TypeSig [])])
                ]
          , dGens = M.empty
          , dCells2 = []
          }
  src <- either (assertFailure . T.unpack) pure (validateDoctrine srcDoc >> Right srcDoc)
  tgt <- either (assertFailure . T.unpack) pure (validateDoctrine tgtDoc >> Right tgtDoc)
  let mor =
        Morphism
          { morName = "BadIxSort"
          , morSrc = src
          , morTgt = tgt
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morAttrSortMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morIxFunMap = M.fromList [(IxFunName "f", IxFunName "g")]
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          , morFuel = 20
          }
  case checkMorphism mor of
    Left err -> assertBool "expected sort mismatch error" ("sort mapping mismatch" `T.isInfixOf` err)
    Right () -> assertFailure "expected morphism check to fail"

testMorphismInstantiationSubstFailure :: Assertion
testMorphismInstantiationSubstFailure = do
  let mode = ModeName "M"
  let aRef = TypeRef mode (TypeName "A")
  let aTy = TCon aRef []
  let srcGen =
        GenDecl
          { gdName = GenName "f"
          , gdMode = mode
          , gdTyVars = []
          , gdIxVars = []
          , gdDom = map InPort [aTy]
          , gdCod = [aTy]
          , gdAttrs = []
          }
  let tgtGen =
        GenDecl
          { gdName = GenName "g"
          , gdMode = mode
          , gdTyVars = []
          , gdIxVars = []
          , gdDom = map InPort [aTy]
          , gdCod = [aTy]
          , gdAttrs = []
          }
  let srcDoc =
        Doctrine
          { dName = "SrcSubstFail"
          , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
          , dIndexModes = S.empty
          , dIxTheory = M.empty
          , dAttrSorts = M.empty
          , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])]
          , dGens = M.fromList [(mode, M.fromList [(GenName "f", srcGen)])]
          , dCells2 = []
          }
  let tgtDoc =
        Doctrine
          { dName = "TgtSubstFail"
          , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
          , dIndexModes = S.empty
          , dIxTheory = M.empty
          , dAttrSorts = M.empty
          , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])]
          , dGens = M.fromList [(mode, M.fromList [(GenName "g", tgtGen)])]
          , dCells2 = []
          }
  src <- case validateDoctrine srcDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure srcDoc
  tgt <- case validateDoctrine tgtDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure tgtDoc
  srcDiag <- either (assertFailure . T.unpack) pure (genD mode [aTy] [aTy] (GenName "f"))
  let badTy = TCon (TypeRef mode (TypeName "Bad")) [TAType aTy]
  badImg <- either (assertFailure . T.unpack) pure (genD mode [badTy] [badTy] (GenName "g"))
  let mor =
        Morphism
          { morName = "SubstFail"
          , morSrc = src
          , morTgt = tgt
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morAttrSortMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.fromList [((mode, GenName "f"), plainImage badImg)]
          , morIxFunMap = M.empty
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          , morFuel = 20
          }
  case applyMorphismDiagram mor srcDiag of
    Left _ -> pure ()
    Right _ -> assertFailure "expected applyMorphismDiagram to fail on substitution error"

testBinderIdentityMorphismPreservesBinders :: Assertion
testBinderIdentityMorphismPreservesBinders = do
  let mode = ModeName "M"
  let lamName = GenName "lam"
  let aTy' = TCon (TypeRef mode (TypeName "A")) []
  let slotSig = BinderSig { bsIxCtx = [], bsDom = [aTy'], bsCod = [aTy'] }
  let lamGen =
        GenDecl
          { gdName = lamName
          , gdMode = mode
          , gdTyVars = []
          , gdIxVars = []
          , gdDom = [InBinder slotSig]
          , gdCod = [aTy']
          , gdAttrs = []
          }
  let doc =
        Doctrine
          { dName = "LamDoc"
          , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
          , dIndexModes = S.empty
          , dIxTheory = M.empty
          , dAttrSorts = M.empty
          , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])]
          , dGens = M.fromList [(mode, M.fromList [(lamName, lamGen)])]
          , dCells2 = []
          }
  doc' <- case validateDoctrine doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure doc
  let body = idD mode [aTy']
  srcDiag0 <- either (assertFailure . T.unpack) pure (genD mode [] [aTy'] lamName)
  srcDiag <- either (assertFailure . T.unpack) pure (setSingleEdgeBargs srcDiag0 [BAConcrete body])
  img0 <- either (assertFailure . T.unpack) pure (genD mode [] [aTy'] lamName)
  let hole = BinderMetaVar "b0"
  img <- either (assertFailure . T.unpack) pure (setSingleEdgeBargs img0 [BAMeta hole])
  let mor =
        Morphism
          { morName = "LamId"
          , morSrc = doc'
          , morTgt = doc'
          , morIsCoercion = False
          , morModeMap = identityModeMap doc'
          , morModMap = identityModMap doc'
          , morAttrSortMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.fromList [((mode, lamName), GenImage img (M.fromList [(hole, slotSig)]))]
          , morIxFunMap = M.empty
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          , morFuel = 20
          }
  case checkMorphism mor of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  mapped <- case applyMorphismDiagram mor srcDiag of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  case IM.elems (dEdges mapped) of
    [Edge _ (PGen g attrs [BAConcrete body']) _ _] -> do
      g @?= lamName
      attrs @?= M.empty
      same <- case diagramIsoEq body body' of
        Left err -> assertFailure (T.unpack err)
        Right ok -> pure ok
      assertBool "expected mapped binder body to be preserved" same
    _ ->
      assertFailure "expected mapped diagram to be a single lam edge with one concrete binder argument"

testMorphismSpliceRenamesToBinderMeta :: Assertion
testMorphismSpliceRenamesToBinderMeta = do
  let mode = ModeName "M"
  let gName = GenName "g"
  let aTy' = TCon (TypeRef mode (TypeName "A")) []
  let slotSig = BinderSig { bsIxCtx = [], bsDom = [aTy'], bsCod = [aTy'] }
  let gDecl =
        GenDecl
          { gdName = gName
          , gdMode = mode
          , gdTyVars = []
          , gdIxVars = []
          , gdDom = [InPort aTy', InBinder slotSig]
          , gdCod = [aTy']
          , gdAttrs = []
          }
  let doc =
        Doctrine
          { dName = "SpliceMetaDoc"
          , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
          , dIndexModes = S.empty
          , dIxTheory = M.empty
          , dAttrSorts = M.empty
          , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])]
          , dGens = M.fromList [(mode, M.fromList [(gName, gDecl)])]
          , dCells2 = []
          }
  doc' <- case validateDoctrine doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure doc
  let xMeta = BinderMetaVar "X"
  let b0 = BinderMetaVar "b0"
  srcDiag0 <- either (assertFailure . T.unpack) pure (genD mode [aTy'] [aTy'] gName)
  srcDiag <- either (assertFailure . T.unpack) pure (setSingleEdgeBargs srcDiag0 [BAMeta xMeta])
  img0 <- either (assertFailure . T.unpack) pure (genD mode [aTy'] [aTy'] (GenName "tmp"))
  img <- either (assertFailure . T.unpack) pure (setSingleEdgePayload img0 (PSplice b0))
  let mor =
        Morphism
          { morName = "SpliceRename"
          , morSrc = doc'
          , morTgt = doc'
          , morIsCoercion = False
          , morModeMap = identityModeMap doc'
          , morModMap = identityModMap doc'
          , morAttrSortMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.fromList [((mode, gName), GenImage img (M.fromList [(b0, slotSig)]))]
          , morIxFunMap = M.empty
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          , morFuel = 20
          }
  case checkMorphism mor of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  mapped <- case applyMorphismDiagram mor srcDiag of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let metas = binderMetaVarsDiagram mapped
  assertBool "expected mapped splice to contain ?X" (xMeta `S.member` metas)
  assertBool "expected mapped splice not to contain ?b0" (S.notMember b0 metas)
  case IM.elems (dEdges mapped) of
    [Edge _ (PSplice x) _ _] -> x @?= xMeta
    _ -> assertFailure "expected mapped image to be a single splice edge"

testMorphismRejectsBadBinderHoleSignatures :: Assertion
testMorphismRejectsBadBinderHoleSignatures = do
  let mode = ModeName "M"
  let lamName = GenName "lam"
  let aTy' = TCon (TypeRef mode (TypeName "A")) []
  let slotSig = BinderSig { bsIxCtx = [], bsDom = [aTy'], bsCod = [aTy'] }
  let wrongSig = BinderSig { bsIxCtx = [], bsDom = [], bsCod = [aTy'] }
  let lamGen =
        GenDecl
          { gdName = lamName
          , gdMode = mode
          , gdTyVars = []
          , gdIxVars = []
          , gdDom = [InBinder slotSig]
          , gdCod = [aTy']
          , gdAttrs = []
          }
  let doc =
        Doctrine
          { dName = "BadBinderSigsDoc"
          , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
          , dIndexModes = S.empty
          , dIxTheory = M.empty
          , dAttrSorts = M.empty
          , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])]
          , dGens = M.fromList [(mode, M.fromList [(lamName, lamGen)])]
          , dCells2 = []
          }
  doc' <- case validateDoctrine doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure doc
  let hole = BinderMetaVar "b0"
  img0 <- either (assertFailure . T.unpack) pure (genD mode [] [aTy'] lamName)
  img <- either (assertFailure . T.unpack) pure (setSingleEdgeBargs img0 [BAMeta hole])
  let mor =
        Morphism
          { morName = "BadBinderSigs"
          , morSrc = doc'
          , morTgt = doc'
          , morIsCoercion = False
          , morModeMap = identityModeMap doc'
          , morModMap = identityModMap doc'
          , morAttrSortMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.fromList [((mode, lamName), GenImage img (M.fromList [(hole, wrongSig)]))]
          , morIxFunMap = M.empty
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          , morFuel = 20
          }
  case checkMorphism mor of
    Left err ->
      assertBool
        "expected binder-hole signature mismatch"
        ("binder-hole signatures mismatch" `T.isInfixOf` err)
    Right () ->
      assertFailure "expected checkMorphism to reject incorrect binder-hole signatures"

testTypeTemplateCycleRejected :: Assertion
testTypeTemplateCycleRejected = do
  let mode = ModeName "M"
  let aRef = TypeRef mode (TypeName "A")
  let bRef = TypeRef mode (TypeName "B")
  let doc =
        Doctrine
          { dName = "CycleDoc"
          , dModes = mkModes [mode]
    , dAcyclicModes = S.empty
          , dIndexModes = S.empty
          , dIxTheory = M.empty
          , dAttrSorts = M.empty
          , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", TypeSig []), (TypeName "B", TypeSig [])])]
          , dGens = M.empty
          , dCells2 = []
          }
  doc' <- case validateDoctrine doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure doc
  let mor =
        Morphism
          { morName = "CycleTypeMap"
          , morSrc = doc'
          , morTgt = doc'
          , morIsCoercion = False
          , morModeMap = identityModeMap doc'
          , morModMap = identityModMap doc'
          , morAttrSortMap = M.empty
          , morTypeMap =
              M.fromList
                [ (aRef, TypeTemplate [] (TCon bRef []))
                , (bRef, TypeTemplate [] (TCon aRef []))
                ]
          , morGenMap = M.empty
          , morIxFunMap = M.empty
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          , morFuel = 20
          }
  case checkMorphism mor of
    Left err ->
      assertBool "expected cyclic type template rejection" ("cyclic type template map" `T.isInfixOf` err)
    Right () ->
      assertFailure "expected checkMorphism to reject cyclic templates"

testIndexedTemplateSortMismatch :: Assertion
testIndexedTemplateSortMismatch = do
  let modeM' = ModeName "M"
  let modeI' = ModeName "I"
  let natRef = TypeRef modeI' (TypeName "Nat")
  let boolRef = TypeRef modeI' (TypeName "Bool")
  let vecRef = TypeRef modeM' (TypeName "Vec")
  let natTy = TCon natRef []
  let boolTy = TCon boolRef []
  let srcDoc =
        Doctrine
          { dName = "SrcSortMismatch"
          , dModes = mkModes [modeM', modeI']
    , dAcyclicModes = S.empty
          , dIndexModes = S.singleton modeI'
          , dIxTheory = M.empty
          , dAttrSorts = M.empty
          , dTypes =
              M.fromList
                [ (modeI', M.fromList [(TypeName "Nat", TypeSig []), (TypeName "Bool", TypeSig [])])
                , (modeM', M.fromList [(TypeName "Vec", TypeSig [PS_Ix natTy, PS_Ty modeM'])])
                ]
          , dGens = M.empty
          , dCells2 = []
          }
  let tgtDoc =
        Doctrine
          { dName = "TgtSortMismatch"
          , dModes = mkModes [modeM', modeI']
    , dAcyclicModes = S.empty
          , dIndexModes = S.singleton modeI'
          , dIxTheory = M.empty
          , dAttrSorts = M.empty
          , dTypes =
              M.fromList
                [ (modeI', M.fromList [(TypeName "Nat", TypeSig []), (TypeName "Bool", TypeSig [])])
                , (modeM', M.fromList [(TypeName "Vec", TypeSig [PS_Ix natTy, PS_Ty modeM'])])
                ]
          , dGens = M.empty
          , dCells2 = []
          }
  src <- case validateDoctrine srcDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure srcDoc
  tgt <- case validateDoctrine tgtDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure tgtDoc
  let nWrong = IxVar { ixvName = "n", ixvSort = boolTy, ixvScope = 0 }
  let aVar = TyVar { tvName = "a", tvMode = modeM' }
  let mor =
        Morphism
          { morName = "SortMismatch"
          , morSrc = src
          , morTgt = tgt
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morAttrSortMap = M.empty
          , morTypeMap =
              M.fromList
                [ ( vecRef
                  , TypeTemplate
                      [TPIx nWrong, TPType aVar]
                      (TVar aVar)
                  )
                ]
          , morGenMap = M.empty
          , morIxFunMap = M.empty
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          , morFuel = 20
          }
  case checkMorphism mor of
    Left err ->
      assertBool "expected index-parameter sort mismatch" ("index-parameter sort mismatch" `T.isInfixOf` err)
    Right () ->
      assertFailure "expected checkMorphism to reject index sort mismatch"

testIndexedTypeTemplateInstantiation :: Assertion
testIndexedTypeTemplateInstantiation = do
  let modeM' = ModeName "M"
  let modeI' = ModeName "I"
  let natRef = TypeRef modeI' (TypeName "Nat")
  let aRef = TypeRef modeM' (TypeName "A")
  let vecRef = TypeRef modeM' (TypeName "Vec")
  let vec2Ref = TypeRef modeM' (TypeName "Vec2")
  let natTy = TCon natRef []
  let aTy' = TCon aRef []
  let z = IXFun (IxFunName "Z") []
  let s x = IXFun (IxFunName "S") [x]
  let ixTheory =
        IxTheory
          { itFuns =
              M.fromList
                [ (IxFunName "Z", IxFunSig [] natTy)
                , (IxFunName "S", IxFunSig [natTy] natTy)
                ]
          , itRules = []
          }
  let srcDoc =
        Doctrine
          { dName = "SrcIndexedTemplate"
          , dModes = mkModes [modeM', modeI']
    , dAcyclicModes = S.empty
          , dIndexModes = S.singleton modeI'
          , dIxTheory = M.fromList [(modeI', ixTheory)]
          , dAttrSorts = M.empty
          , dTypes =
              M.fromList
                [ (modeI', M.fromList [(TypeName "Nat", TypeSig [])])
                , ( modeM'
                  , M.fromList
                      [ (TypeName "A", TypeSig [])
                      , (TypeName "Vec", TypeSig [PS_Ix natTy, PS_Ty modeM'])
                      ]
                  )
                ]
          , dGens = M.empty
          , dCells2 = []
          }
  let tgtDoc =
        Doctrine
          { dName = "TgtIndexedTemplate"
          , dModes = mkModes [modeM', modeI']
    , dAcyclicModes = S.empty
          , dIndexModes = S.singleton modeI'
          , dIxTheory = M.fromList [(modeI', ixTheory)]
          , dAttrSorts = M.empty
          , dTypes =
              M.fromList
                [ (modeI', M.fromList [(TypeName "Nat", TypeSig [])])
                , ( modeM'
                  , M.fromList
                      [ (TypeName "A", TypeSig [])
                      , (TypeName "Vec2", TypeSig [PS_Ix natTy, PS_Ty modeM'])
                      ]
                  )
                ]
          , dGens = M.empty
          , dCells2 = []
          }
  src <- case validateDoctrine srcDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure srcDoc
  tgt <- case validateDoctrine tgtDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure tgtDoc
  let nVar = IxVar { ixvName = "n", ixvSort = natTy, ixvScope = 0 }
  let aVar = TyVar { tvName = "a", tvMode = modeM' }
  let mor =
        Morphism
          { morName = "MapVec"
          , morSrc = src
          , morTgt = tgt
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morAttrSortMap = M.empty
          , morTypeMap =
              M.fromList
                [ ( vecRef
                  , TypeTemplate
                      [TPIx nVar, TPType aVar]
                      (TCon vec2Ref [TAIndex (s (IXVar nVar)), TAType (TVar aVar)])
                  )
                ]
          , morGenMap = M.empty
          , morIxFunMap = M.empty
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          , morFuel = 20
          }
  case checkMorphism mor of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  let srcDiag = idD modeM' [TCon vecRef [TAIndex z, TAType aTy']]
  tgtDiag <- case applyMorphismDiagram mor srcDiag of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  dom <- case diagramDom tgtDiag of
    Left err -> assertFailure (T.unpack err)
    Right ctx -> pure ctx
  dom @?= [TCon vec2Ref [TAIndex (s z), TAType aTy']]

testIndexedTemplateKindMismatch :: Assertion
testIndexedTemplateKindMismatch = do
  let modeM' = ModeName "M"
  let modeI' = ModeName "I"
  let natRef = TypeRef modeI' (TypeName "Nat")
  let vecRef = TypeRef modeM' (TypeName "Vec")
  let vec2Ref = TypeRef modeM' (TypeName "Vec2")
  let natTy = TCon natRef []
  let ixTheory =
        IxTheory
          { itFuns = M.empty
          , itRules = []
          }
  let srcDoc =
        Doctrine
          { dName = "SrcIndexedTemplateBad"
          , dModes = mkModes [modeM', modeI']
    , dAcyclicModes = S.empty
          , dIndexModes = S.singleton modeI'
          , dIxTheory = M.fromList [(modeI', ixTheory)]
          , dAttrSorts = M.empty
          , dTypes =
              M.fromList
                [ (modeI', M.fromList [(TypeName "Nat", TypeSig [])])
                , (modeM', M.fromList [(TypeName "Vec", TypeSig [PS_Ix natTy, PS_Ty modeM'])])
                ]
          , dGens = M.empty
          , dCells2 = []
          }
  let tgtDoc =
        Doctrine
          { dName = "TgtIndexedTemplateBad"
          , dModes = mkModes [modeM', modeI']
    , dAcyclicModes = S.empty
          , dIndexModes = S.singleton modeI'
          , dIxTheory = M.fromList [(modeI', ixTheory)]
          , dAttrSorts = M.empty
          , dTypes =
              M.fromList
                [ (modeI', M.fromList [(TypeName "Nat", TypeSig [])])
                , (modeM', M.fromList [(TypeName "Vec2", TypeSig [PS_Ix natTy, PS_Ty modeM'])])
                ]
          , dGens = M.empty
          , dCells2 = []
          }
  src <- case validateDoctrine srcDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure srcDoc
  tgt <- case validateDoctrine tgtDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure tgtDoc
  let nVar = IxVar { ixvName = "n", ixvSort = natTy, ixvScope = 0 }
  let aVar = TyVar { tvName = "a", tvMode = modeM' }
  let mor =
        Morphism
          { morName = "BadKind"
          , morSrc = src
          , morTgt = tgt
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morAttrSortMap = M.empty
          , morTypeMap =
              M.fromList
                [ ( vecRef
                  , TypeTemplate
                      [TPType aVar, TPIx nVar]
                      (TCon vec2Ref [TAIndex (IXVar nVar), TAType (TVar aVar)])
                  )
                ]
          , morGenMap = M.empty
          , morIxFunMap = M.empty
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          , morFuel = 20
          }
  case checkMorphism mor of
    Left err ->
      assertBool "expected template kind mismatch" ("kind mismatch" `T.isInfixOf` err)
    Right () ->
      assertFailure "expected morphism check to fail"

modeM :: ModeName
modeM = ModeName "M"

aTy :: TypeExpr
aTy = TCon (TypeRef modeM (TypeName "A")) []

strTy :: TypeExpr
strTy = TCon (TypeRef modeM (TypeName "Str")) []

mkMonoid :: Either Text Doctrine
mkMonoid = do
  let mt = mkModes [modeM]
  let types = M.fromList [(modeM, M.fromList [(TypeName "A", TypeSig [])])]
  assoc <- assocRule "assoc" aTy (GenName "mul")
  unitL <- unitRule "unitL" aTy (GenName "unit") (GenName "mul") True
  unitR <- unitRule "unitR" aTy (GenName "unit") (GenName "mul") False
  let gens =
        M.fromList
          [ ( modeM
            , M.fromList
                [ ( GenName "unit"
                  , GenDecl
                      { gdName = GenName "unit"
                      , gdMode = modeM
                      , gdTyVars = []
                      , gdIxVars = []
                      , gdDom = map InPort []
                      , gdCod = [aTy]
                      , gdAttrs = []
                      }
                  )
                , ( GenName "mul"
                  , GenDecl
                      { gdName = GenName "mul"
                      , gdMode = modeM
                      , gdTyVars = []
                      , gdIxVars = []
                      , gdDom = map InPort [aTy, aTy]
                      , gdCod = [aTy]
                      , gdAttrs = []
                      }
                  )
                ]
            )
          ]
  let doc = Doctrine
        { dName = "Monoid"
        , dModes = mt
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
      , dAttrSorts = M.empty
        , dTypes = types
        , dGens = gens
        , dCells2 = [assoc, unitL, unitR]
        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc

mkStringMonoid :: Either Text Doctrine
mkStringMonoid = do
  let mt = mkModes [modeM]
  let types = M.fromList [(modeM, M.fromList [(TypeName "Str", TypeSig [])])]
  assoc <- assocRule "assoc" strTy (GenName "append")
  unitL <- unitRule "unitL" strTy (GenName "empty") (GenName "append") True
  unitR <- unitRule "unitR" strTy (GenName "empty") (GenName "append") False
  let gens =
        M.fromList
          [ ( modeM
            , M.fromList
                [ ( GenName "empty"
                  , GenDecl
                      { gdName = GenName "empty"
                      , gdMode = modeM
                      , gdTyVars = []
                      , gdIxVars = []
                      , gdDom = map InPort []
                      , gdCod = [strTy]
                      , gdAttrs = []
                      }
                  )
                , ( GenName "append"
                  , GenDecl
                      { gdName = GenName "append"
                      , gdMode = modeM
                      , gdTyVars = []
                      , gdIxVars = []
                      , gdDom = map InPort [strTy, strTy]
                      , gdCod = [strTy]
                      , gdAttrs = []
                      }
                  )
                ]
            )
          ]
  let doc = Doctrine
        { dName = "StringMonoid"
        , dModes = mt
    , dAcyclicModes = S.empty
      , dIndexModes = S.empty
      , dIxTheory = M.empty
      , dAttrSorts = M.empty
        , dTypes = types
        , dGens = gens
        , dCells2 = [assoc, unitL, unitR]
        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc

assocRule :: Text -> TypeExpr -> GenName -> Either Text Cell2
assocRule name ty mulName = do
  mul <- genD modeM [ty, ty] [ty] mulName
  id1 <- pure (idD modeM [ty])
  left <- tensorD mul id1
  lhs <- compDTT (modeOnlyTypeTheory (mkModes [modeM])) mul left
  right <- tensorD id1 mul
  rhs <- compDTT (modeOnlyTypeTheory (mkModes [modeM])) mul right
  pure Cell2
    { c2Name = name
    , c2Class = Computational
    , c2Orient = LR
    , c2TyVars = []
    , c2IxVars = []
    , c2LHS = lhs
    , c2RHS = rhs
    }

unitRule :: Text -> TypeExpr -> GenName -> GenName -> Bool -> Either Text Cell2
unitRule name ty unitName mulName leftSide = do
  unit <- genD modeM [] [ty] unitName
  mul <- genD modeM [ty, ty] [ty] mulName
  id1 <- pure (idD modeM [ty])
  expr <-
    if leftSide
      then do
        tens <- tensorD unit id1
        compDTT (modeOnlyTypeTheory (mkModes [modeM])) mul tens
      else do
        tens <- tensorD id1 unit
        compDTT (modeOnlyTypeTheory (mkModes [modeM])) mul tens
  pure Cell2
    { c2Name = name
    , c2Class = Computational
    , c2Orient = LR
    , c2TyVars = []
    , c2IxVars = []
    , c2LHS = expr
    , c2RHS = id1
    }

testMorphismCheckAllEnforcesComputational :: Assertion
testMorphismCheckAllEnforcesComputational =
  case elabProgram morphismCheckAllProgram of
    Left err ->
      assertBool "expected equation-preservation failure" ("equation" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected morphism elaboration to fail under check all"

testMorphismCheckStructuralIgnoresComputational :: Assertion
testMorphismCheckStructuralIgnoresComputational =
  case elabProgram morphismCheckStructuralProgram of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testMorphismCheckNoneSkipsStructural :: Assertion
testMorphismCheckNoneSkipsStructural =
  case elabProgram morphismCheckNoneProgram of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testMorphismRejectsBadGenImageBoundaryAtElab :: Assertion
testMorphismRejectsBadGenImageBoundaryAtElab =
  case elabProgram morphismBadBoundaryProgram of
    Left err ->
      assertBool
        "expected generator-image boundary mismatch"
        ("length mismatch" `T.isInfixOf` err || "boundary mismatch" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected morphism elaboration to reject a wrong-boundary generator image"

testWireMetaRuleElaborates :: Assertion
testWireMetaRuleElaborates =
  case elabProgram wireMetaRuleProgram of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testWireMetaRuleRejectsDuplicateName :: Assertion
testWireMetaRuleRejectsDuplicateName =
  case elabProgram wireMetaDuplicateProgram of
    Left err ->
      assertBool
        "expected duplicate wire metavariable rejection"
        ("diagram metavariable `?x` used more than once" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected duplicate wire metavariable usage to fail"

elabProgram :: Text -> Either Text ()
elabProgram src = do
  raw <- parseRawFile src
  _ <- elabRawFile raw
  pure ()

morphismCheckAllProgram :: Text
morphismCheckAllProgram =
  "doctrine S where {\n"
    <> "  mode M;\n"
    <> "  type B @M;\n"
    <> "  gen f : [B] -> [B] @M;\n"
    <> "  rule computational f_id -> : [B] -> [B] @M =\n"
    <> "    f == id[B]\n"
    <> "}\n"
    <> "doctrine T where {\n"
    <> "  mode M;\n"
    <> "  type B @M;\n"
    <> "  gen g : [B] -> [B] @M;\n"
    <> "}\n"
    <> "morphism m : S -> T where {\n"
    <> "  check all;\n"
    <> "  mode M -> M;\n"
    <> "  gen f @M -> g\n"
    <> "}\n"

morphismCheckStructuralProgram :: Text
morphismCheckStructuralProgram =
  T.replace "check all;" "check structural;" morphismCheckAllProgram

morphismCheckNoneProgram :: Text
morphismCheckNoneProgram =
  T.replace
    "rule computational f_id -> : [B] -> [B] @M =\n    f == id[B]"
    "rule structural f_id -> : [B] -> [B] @M =\n    f == id[B]"
    (T.replace "check all;" "check none;" morphismCheckAllProgram)

morphismBadBoundaryProgram :: Text
morphismBadBoundaryProgram =
  "doctrine S where {\n"
    <> "  mode M;\n"
    <> "  type B @M;\n"
    <> "  gen and : [B, B] -> [B] @M;\n"
    <> "}\n"
    <> "doctrine T where {\n"
    <> "  mode M;\n"
    <> "  type B @M;\n"
    <> "  gen true : [] -> [B] @M;\n"
    <> "}\n"
    <> "morphism bad : S -> T where {\n"
    <> "  check none;\n"
    <> "  mode M -> M;\n"
    <> "  gen and @M -> true\n"
    <> "}\n"

wireMetaRuleProgram :: Text
wireMetaRuleProgram =
  "doctrine D where {\n"
    <> "  mode M;\n"
    <> "  type B @M;\n"
    <> "  gen true : [] -> [B] @M;\n"
    <> "  gen and : [B, B] -> [B] @M;\n"
    <> "  rule computational and_true_r -> : [B] -> [B] @M =\n"
    <> "    (true * ?x) ; and == ?x\n"
    <> "}\n"

wireMetaDuplicateProgram :: Text
wireMetaDuplicateProgram =
  "doctrine D where {\n"
    <> "  mode M;\n"
    <> "  type B @M;\n"
    <> "  gen true : [] -> [B] @M;\n"
    <> "  gen and : [B, B] -> [B] @M;\n"
    <> "  rule computational and_bad -> : [B] -> [B] @M =\n"
    <> "    (true * ?x) ; and == (?x * ?x) ; and\n"
    <> "}\n"
