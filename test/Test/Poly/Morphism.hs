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
import Strat.Poly.Obj
import Strat.Poly.Names
import Strat.Poly.Diagram
import Strat.Poly.Graph (Edge(..), EdgePayload(..), BinderArg(..), BinderMetaVar(..), emptyDiagram, freshPort, addEdgePayload)
import Strat.Poly.DiagramIso (diagramIsoEq)
import Strat.Poly.Cell2
import Strat.Poly.Doctrine
import Strat.Poly.Morphism
import Strat.Poly.TypeTheory (modeOnlyTypeTheory, TypeParamSig(..))
import Strat.Poly.TermExpr (TermExpr(..), termExprToDiagram, diagramToTermExpr)
import Test.Poly.Helpers (mkModes, identityModeMap, identityModMap)


tests :: TestTree
tests =
  testGroup
    "Poly.Morphism"
    [ testCase "monoid morphism to string monoid" testMonoidMorphism
    , testCase "type map can reorder parameters" testTypeMapReorder
    , testCase "cross-mode morphism applies mode map" testCrossModeMorphism
    , testCase "modality map rewrites modality applications in types" testModalityMapRewritesTypeModalities
    , testCase "morphism type mapping rejects missing target constructor" testMorphismRejectsMissingTargetCtor
    , testCase "morphism requires explicit mappings for comprehension support generators" testMorphismRequiresExplicitComprehensionMappings
    , testCase "morphism instantiation fails on dependent substitution errors" testMorphismInstantiationSubstFailure
    , testCase "binder generator identity morphism preserves binder arguments" testBinderIdentityMorphismPreservesBinders
    , testCase "morphism rewrites splice binder holes to substituted binder metas" testMorphismSpliceRenamesToBinderMeta
    , testCase "morphism checker rejects incorrect binder-hole signatures" testMorphismRejectsBadBinderHoleSignatures
    , testCase "morphism rejects cyclic type templates" testTypeTemplateCycleRejected
    , testCase "morphism rejects term-template sort mismatch in same mode" testTermTemplateSortMismatch
    , testCase "morphism type map instantiates term-templates" testTermTypeTemplateInstantiation
    , testCase "morphism rejects term-template parameter kind mismatch" testTermTemplateKindMismatch
    , testCase "morphism maps structured term arguments inside types" testMorphismMapsStructuredTermArgs
    , testCase "morphism weakens image term-context prefixes before splice" testMorphismWeakenImageTmCtx
    , testCase "morphism check all enforces computational equations" testMorphismCheckAllEnforcesComputational
    , testCase "morphism check structural ignores computational equations" testMorphismCheckStructuralIgnoresComputational
    , testCase "morphism check none skips structural equations" testMorphismCheckNoneSkipsStructural
    , testCase "morphism rejects classifier-edge mismatch" testMorphismRejectsClassifierEdgeMismatch
    , testCase "morphism elaboration rejects generator images with wrong boundaries" testMorphismRejectsBadGenImageBoundaryAtElab
    , testCase "wire metavariable rules elaborate" testWireMetaRuleElaborates
    , testCase "wire metavariables reject duplicate names in one diagram" testWireMetaRuleRejectsDuplicateName
    ]

tvar :: ModeName -> Text -> TmVar
tvar mode name = mkModeMetaVar name mode

universeName :: ModeName -> ObjName
universeName (ModeName n) = ObjName ("U_" <> n)

universeObj :: ModeName -> Obj
universeObj mode = mkCon (ObjRef mode (universeName mode)) []

selfClassifiedModes :: [ModeName] -> ModeTheory
selfClassifiedModes modes =
  let mt = mkModes modes
  in mt
       { mtClassifiedBy =
           M.fromList
             [ (mode, ClassificationDecl { cdClassifier = mode, cdUniverse = universeObj mode, cdComp = Just compDecl })
             | mode <- modes
             ]
       }

objNameText :: ObjName -> Text
objNameText (ObjName n) = n

ctorDecl :: ModeName -> ObjName -> [TypeParamSig] -> GenDecl
ctorDecl mode ctorName sig =
  GenDecl
    { gdName = GenName (objNameText ctorName)
    , gdMode = mode
    , gdParams = params
    , gdDom = []
    , gdCod = [universeObj mode]
    , gdAttrs = []
    }
  where
    tyPos =
      [ (pos, v)
      | (pos, TPS_Ty m) <- zip [0 :: Int ..] sig
      , let v =
              TmVar
                { tmvName = "a" <> T.pack (show pos)
                , tmvSort = universeObj m
                , tmvScope = 0
                , tmvOwnerMode = Just m
                }
      ]
    tmPos =
      [ (pos, v)
      | (pos, TPS_Tm sortTy) <- zip [0 :: Int ..] sig
      , let v =
              TmVar
                { tmvName = "x" <> T.pack (show pos)
                , tmvSort = sortTy
                , tmvScope = 0
                , tmvOwnerMode = Just mode
                }
      ]
    tyVars = map snd tyPos
    tmVars = map snd tmPos
    params =
      [ case ps of
          TPS_Ty _ -> GP_Ty (lookupByPos pos tyPos)
          TPS_Tm _ -> GP_Tm (lookupByPos pos tmPos)
      | (pos, ps) <- zip [0 :: Int ..] sig
      ]
    lookupByPos pos xs =
      case lookup pos xs of
        Just v -> v
        Nothing -> error "ctorDecl: missing parameter position"

addSelfClassifications :: [ModeName] -> ModeTheory -> ModeTheory
addSelfClassifications modes mt =
  mt
    { mtClassifiedBy =
        foldl
          (\acc mode ->
              M.insertWith
                (\_ old -> old)
                mode
                (ClassificationDecl { cdClassifier = mode, cdUniverse = universeObj mode, cdComp = Just compDecl })
                acc
          )
          (mtClassifiedBy mt)
          modes
    }

insertCtorDecls
  :: ModeName
  -> [(ObjName, [TypeParamSig])]
  -> M.Map ModeName (M.Map GenName GenDecl)
  -> M.Map ModeName (M.Map GenName GenDecl)
insertCtorDecls mode sigs gens0 =
  let ctorMap =
        M.fromList
          [ (gdName gd, gd)
          | (ctorName, sig) <- sigs
          , let gd = ctorDecl mode ctorName sig
          ]
      modeMap = M.findWithDefault M.empty mode gens0
   in M.insert mode (M.union modeMap ctorMap) gens0

withSelfClassifiedCtors :: [(ModeName, [(ObjName, [TypeParamSig])])] -> Doctrine -> Doctrine
withSelfClassifiedCtors entries doc =
  doc
    { dModes = addSelfClassifications (map fst entries) (dModes doc)
    , dGens =
        foldl
          (\acc (mode, sigs) -> insertCompSupportGens mode (insertCtorDecls mode sigs acc))
          (dGens doc)
          entries
    }

compCtxExtName :: GenName
compCtxExtName = GenName "__ctx_ext"

compVarName :: GenName
compVarName = GenName "__var"

compReindexName :: GenName
compReindexName = GenName "__reindex"

compDecl :: CompDecl
compDecl =
  CompDecl
    { compCtxExt = compCtxExtName
    , compVar = compVarName
    , compReindex = compReindexName
    }

mkCompGen :: ModeName -> Obj -> GenName -> GenDecl
mkCompGen mode aTy name =
  GenDecl
    { gdName = name
    , gdMode = mode
    , gdParams = []
    , gdDom = [InPort aTy]
    , gdCod = [aTy]
    , gdAttrs = []
    }

insertCompSupportGens
  :: ModeName
  -> M.Map ModeName (M.Map GenName GenDecl)
  -> M.Map ModeName (M.Map GenName GenDecl)
insertCompSupportGens mode gens0 =
  let modeGens = M.findWithDefault M.empty mode gens0
      aTy = universeObj mode
      support =
        [ mkCompGen mode aTy compCtxExtName
        , mkCompGen mode aTy compVarName
        , mkCompGen mode aTy compReindexName
        ]
      modeGens' = foldl (\acc gd -> M.insertWith (\_ old -> old) (gdName gd) gd acc) modeGens support
   in M.insert mode modeGens' gens0

attachComprehensionFixture :: ModeName -> Obj -> Doctrine -> Doctrine
attachComprehensionFixture mode aTy doc =
  let modeGens0 = M.findWithDefault M.empty mode (dGens doc)
      compGens =
        [ mkCompGen mode aTy compCtxExtName
        , mkCompGen mode aTy compVarName
        , mkCompGen mode aTy compReindexName
        ]
      modeGens1 = foldl (\acc gd -> M.insert (gdName gd) gd acc) modeGens0 compGens
      modes0 = dModes doc
      classDecl0 = M.findWithDefault defaultClassDecl mode (mtClassifiedBy modes0)
      classDecl1 =
        classDecl0
          { cdComp =
              Just
                CompDecl
                  { compCtxExt = compCtxExtName
                  , compVar = compVarName
                  , compReindex = compReindexName
                  }
          }
      modes1 = modes0 { mtClassifiedBy = M.insert mode classDecl1 (mtClassifiedBy modes0) }
   in doc { dModes = modes1, dGens = M.insert mode modeGens1 (dGens doc) }
  where
    defaultClassDecl =
      ClassificationDecl
        { cdClassifier = mode
        , cdUniverse = universeObj mode
        
        , cdComp = Just compDecl
        }

compIdentityImagesMapped :: ModeName -> ModeName -> Obj -> Either Text [((ModeName, GenName), GenImage)]
compIdentityImagesMapped srcMode tgtMode aTy = do
  ctxExtImg <- plainImage <$> genD tgtMode [aTy] [aTy] compCtxExtName
  varImg <- plainImage <$> genD tgtMode [aTy] [aTy] compVarName
  reindexImg <- plainImage <$> genD tgtMode [aTy] [aTy] compReindexName
  pure
    [ ((srcMode, compCtxExtName), ctxExtImg)
    , ((srcMode, compVarName), varImg)
    , ((srcMode, compReindexName), reindexImg)
    ]

compIdentityImages :: ModeName -> Obj -> Either Text [((ModeName, GenName), GenImage)]
compIdentityImages mode = compIdentityImagesMapped mode mode

tcon :: ModeName -> Text -> [Obj] -> Obj
tcon mode name args = mkCon (ObjRef mode (ObjName name)) (map OAObj args)

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

tmMeta :: TmVar -> TermDiagram
tmMeta v =
  let mode = objMode (tmvSort v)
      (outPid, d0) = freshPort (tmvSort v) (emptyDiagram mode [])
      d1 =
        case addEdgePayload (PTmMeta v) [] [outPid] d0 of
          Left err -> error (T.unpack err)
          Right d -> d
  in TermDiagram d1 { dOut = [outPid] }

normalizeDoctrine :: Doctrine -> Doctrine
normalizeDoctrine = id

normalizeMorphism :: Morphism -> Morphism
normalizeMorphism mor =
  mor
    { morSrc = normalizeDoctrine (morSrc mor)
    , morTgt = normalizeDoctrine (morTgt mor)
    }

validateDoctrineNormalized :: Doctrine -> Either Text ()
validateDoctrineNormalized = validateDoctrine . normalizeDoctrine

checkMorphismNormalized mor = checkMorphism (normalizeMorphism mor)

applyMorphismDiagramNormalized :: Morphism -> Diagram -> Either Text Diagram
applyMorphismDiagramNormalized mor = applyMorphismDiagram (normalizeMorphism mor)

applyMorphismTyNormalized :: Morphism -> Obj -> Either Text Obj
applyMorphismTyNormalized mor = applyMorphismTy (normalizeMorphism mor)

testMonoidMorphism :: Assertion
testMonoidMorphism = do
  docSrc <- either (assertFailure . T.unpack) pure mkMonoid
  docTgt <- either (assertFailure . T.unpack) pure mkStringMonoid
  let modeMap = identityModeMap docSrc
  compImgs <- either (assertFailure . T.unpack) pure (compIdentityImages modeM (universeObj modeM))
  let typeMap = M.fromList [(ObjRef modeM (ObjName "A"), TypeTemplate [] (tcon modeM "Str" []))]
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
        , morGenMap =
            M.fromList
              ( [ ((modeM, GenName "unit"), plainImage unitImg)
                , ((modeM, GenName "mul"), plainImage mulImg)
                ]
                  <> compImgs
              )
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        }
  case checkMorphismNormalized mor of
    Left err -> assertFailure (show err)
    Right () -> pure ()

testTypeMapReorder :: Assertion
testTypeMapReorder = do
  let mode = ModeName "M"
  let uTy = universeObj mode
  let a = TmVar { tmvName = "a", tmvSort = uTy, tmvScope = 0, tmvOwnerMode = Just mode }
  let b = TmVar { tmvName = "b", tmvSort = uTy, tmvScope = 0, tmvOwnerMode = Just mode }
  let prod = ObjName "Prod"
  let pair = ObjName "Pair"
  let genName = GenName "g"
  let genSrc =
        GenDecl
          { gdName = genName
          , gdMode = mode
          , gdParams = [GP_Ty a, GP_Ty b]
          , gdDom = map InPort [mkCon (ObjRef mode prod) [OAObj (OVar (a)), OAObj (OVar (b))]]
          , gdCod = [mkCon (ObjRef mode prod) [OAObj (OVar (a)), OAObj (OVar (b))]]
          , gdAttrs = []
          }
  let genTgt =
        GenDecl
          { gdName = genName
          , gdMode = mode
          , gdParams = [GP_Ty a, GP_Ty b]
          , gdDom = map InPort [mkCon (ObjRef mode pair) [OAObj (OVar (a)), OAObj (OVar (b))]]
          , gdCod = [mkCon (ObjRef mode pair) [OAObj (OVar (a)), OAObj (OVar (b))]]
          , gdAttrs = []
          }
  let prodCtor =
        GenDecl
          { gdName = GenName "Prod"
          , gdMode = mode
          , gdParams = [GP_Ty a, GP_Ty b]
          , gdDom = []
          , gdCod = [uTy]
          , gdAttrs = []
          }
  let pairCtor =
        GenDecl
          { gdName = GenName "Pair"
          , gdMode = mode
          , gdParams = [GP_Ty a, GP_Ty b]
          , gdDom = []
          , gdCod = [uTy]
          , gdAttrs = []
          }
  let docSrc = Doctrine
        { dName = "Src"
        , dModes = selfClassifiedModes [mode]
        , dAcyclicModes = S.empty
        , dAttrSorts = M.empty
        , dGens =
            insertCompSupportGens mode $
              M.fromList [(mode, M.fromList [(gdName prodCtor, prodCtor), (genName, genSrc)])]
        , dCells2 = []
        , dActions = M.empty
        , dObligations = []
        }
  let docTgt = Doctrine
        { dName = "Tgt"
        , dModes = selfClassifiedModes [mode]
        , dAcyclicModes = S.empty
        , dAttrSorts = M.empty
        , dGens =
            insertCompSupportGens mode $
              M.fromList [(mode, M.fromList [(gdName pairCtor, pairCtor), (genName, genTgt)])]
        , dCells2 = []
        , dActions = M.empty
        , dObligations = []
        }
  docSrc' <- case validateDoctrineNormalized docSrc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docSrc
  docTgt' <- case validateDoctrineNormalized docTgt of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docTgt
  compImgs <- either (assertFailure . T.unpack) pure (compIdentityImages mode (universeObj mode))
  img <- either (assertFailure . T.unpack) pure (genD mode [mkCon (ObjRef mode pair) [OAObj (OVar (b)), OAObj (OVar (a))]] [mkCon (ObjRef mode pair) [OAObj (OVar (b)), OAObj (OVar (a))]] genName)
  let typeMap = M.fromList [(ObjRef mode prod, TypeTemplate [GP_Ty a, GP_Ty b] (mkCon (ObjRef mode pair) [OAObj (OVar (b)), OAObj (OVar (a))]))]
  let mor = Morphism
        { morName = "SwapProd"
        , morSrc = docSrc'
        , morTgt = docTgt'
        , morIsCoercion = False
        , morModeMap = identityModeMap docSrc'
        , morModMap = identityModMap docSrc'
        , morAttrSortMap = M.empty
        , morTypeMap = typeMap
        , morGenMap = M.fromList (((mode, genName), plainImage img) : compImgs)
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        }
  case checkMorphismNormalized mor of
    Left err -> assertFailure (show err)
    Right () -> pure ()

testCrossModeMorphism :: Assertion
testCrossModeMorphism = do
  let modeC = ModeName "C"
  let modeV = ModeName "V"
  let aRef = ObjRef modeC (ObjName "A")
  let bRef = ObjRef modeV (ObjName "B")
  let aTy = mkCon aRef []
  let bTy = mkCon bRef []
  let fGen =
        GenDecl
          { gdName = GenName "f"
          , gdMode = modeC
          , gdParams = []
          , gdDom = map InPort [aTy]
          , gdCod = [aTy]
          , gdAttrs = []
          }
  let gGen =
        GenDecl
          { gdName = GenName "g"
          , gdMode = modeV
          , gdParams = []
          , gdDom = map InPort [bTy]
          , gdCod = [bTy]
          , gdAttrs = []
          }
  let docSrc =
        withSelfClassifiedCtors
          [(modeC, [(ObjName "A", [])])]
          Doctrine
            { dName = "Src"
            , dModes = mkModes [modeC]
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.fromList [(modeC, M.fromList [(GenName "f", fGen)])]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  let docTgt =
        withSelfClassifiedCtors
          [(modeV, [(ObjName "B", [])])]
          Doctrine
            { dName = "Tgt"
            , dModes = mkModes [modeV]
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.fromList [(modeV, M.fromList [(GenName "g", gGen)])]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  docSrc' <- case validateDoctrineNormalized docSrc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docSrc
  docTgt' <- case validateDoctrineNormalized docTgt of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docTgt
  compImgs <- either (assertFailure . T.unpack) pure (compIdentityImagesMapped modeC modeV (universeObj modeV))
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
        , morGenMap = M.fromList (((modeC, GenName "f"), plainImage img) : compImgs)
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        }
  case checkMorphismNormalized mor of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  srcDiag <- either (assertFailure . T.unpack) pure (genD modeC [aTy] [aTy] (GenName "f"))
  tgtDiag <- either (assertFailure . T.unpack) pure (applyMorphismDiagramNormalized mor srcDiag)
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
  let fBaseSrc = OMod fSrc baseSrc
  let hfBaseSrc = OMod hSrc fBaseSrc
  let gBaseTgt = OMod gTgt baseTgt
  let kgBaseTgt = OMod kTgt gBaseTgt
  let gkBaseTgt = OMod (ModExpr { meSrc = modeC, meTgt = modeD, mePath = [modG, modK] }) baseTgt
  let modeTheorySrc =
        ModeTheory
          { mtModes =
              M.fromList
                [ (modeA, ModeInfo { miName = modeA, miDefEqEngine = DefEqTRS })
                , (modeB, ModeInfo { miName = modeB, miDefEqEngine = DefEqTRS })
                ]
          , mtDecls =
              M.fromList
                [ (modF, ModDecl modF modeA modeB)
                , (modH, ModDecl modH modeB modeB)
                ]
          , mtEqns = []
          , mtTransforms = M.empty
          , mtClassifiedBy = M.empty
          , mtClassifierLifts = M.empty
          }
  let modeTheoryTgt =
        ModeTheory
          { mtModes =
              M.fromList
                [ (modeC, ModeInfo { miName = modeC, miDefEqEngine = DefEqTRS })
                , (modeD, ModeInfo { miName = modeD, miDefEqEngine = DefEqTRS })
                ]
          , mtDecls =
              M.fromList
                [ (modG, ModDecl modG modeC modeD)
                , (modK, ModDecl modK modeD modeD)
                ]
          , mtEqns = []
          , mtTransforms = M.empty
          , mtClassifiedBy = M.empty
          , mtClassifierLifts = M.empty
          }
  let genGSrc =
        GenDecl
          { gdName = GenName "g"
          , gdMode = modeB
          , gdParams = []
          , gdDom = map InPort [fBaseSrc]
          , gdCod = [fBaseSrc]
          , gdAttrs = []
          }
  let genGGSrc =
        GenDecl
          { gdName = GenName "gg"
          , gdMode = modeB
          , gdParams = []
          , gdDom = map InPort [hfBaseSrc]
          , gdCod = [hfBaseSrc]
          , gdAttrs = []
          }
  let genGTgt =
        GenDecl
          { gdName = GenName "g"
          , gdMode = modeD
          , gdParams = []
          , gdDom = map InPort [gBaseTgt]
          , gdCod = [gBaseTgt]
          , gdAttrs = []
          }
  let genGGTgt =
        GenDecl
          { gdName = GenName "gg"
          , gdMode = modeD
          , gdParams = []
          , gdDom = map InPort [kgBaseTgt]
          , gdCod = [kgBaseTgt]
          , gdAttrs = []
          }
  let docSrc =
        withSelfClassifiedCtors
          [(modeA, [(ObjName "Base", [])])]
          Doctrine
            { dName = "SrcModal"
            , dModes = modeTheorySrc
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.fromList [(modeB, M.fromList [(GenName "g", genGSrc), (GenName "gg", genGGSrc)])]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  let docTgt =
        withSelfClassifiedCtors
          [(modeC, [(ObjName "Base", [])])]
          Doctrine
            { dName = "TgtModal"
            , dModes = modeTheoryTgt
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.fromList [(modeD, M.fromList [(GenName "g", genGTgt), (GenName "gg", genGGTgt)])]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  docSrc' <- case validateDoctrineNormalized docSrc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docSrc
  docTgt' <- case validateDoctrineNormalized docTgt of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docTgt
  compImgs <- either (assertFailure . T.unpack) pure (compIdentityImagesMapped modeA modeC (universeObj modeC))
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
        , morTypeMap = M.fromList [(ObjRef modeA (ObjName "Base"), TypeTemplate [] baseTgt)]
        , morGenMap =
            M.fromList
              ( [ ((modeB, GenName "g"), plainImage imgG)
                , ((modeB, GenName "gg"), plainImage imgGG)
                ]
                  <> compImgs
              )
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        }
  case checkMorphismNormalized mor of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()

  srcDiagG <- either (assertFailure . T.unpack) pure (genD modeB [fBaseSrc] [fBaseSrc] (GenName "g"))
  tgtDiagG <- either (assertFailure . T.unpack) pure (applyMorphismDiagramNormalized mor srcDiagG)
  dMode tgtDiagG @?= modeD
  domG <- either (assertFailure . T.unpack) pure (diagramDom tgtDiagG)
  codG <- either (assertFailure . T.unpack) pure (diagramCod tgtDiagG)
  domG @?= [gBaseTgt]
  codG @?= [gBaseTgt]
  assertSingleGenEdge "g" tgtDiagG

  srcDiagGG <- either (assertFailure . T.unpack) pure (genD modeB [hfBaseSrc] [hfBaseSrc] (GenName "gg"))
  tgtDiagGG <- either (assertFailure . T.unpack) pure (applyMorphismDiagramNormalized mor srcDiagGG)
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

testMorphismRejectsMissingTargetCtor :: Assertion
testMorphismRejectsMissingTargetCtor = do
  let mode = ModeName "M"
  let srcDoc =
        withSelfClassifiedCtors
          [(mode, [(ObjName "T", [])])]
          Doctrine
            { dName = "SrcMissingCtor"
            , dModes = mkModes [mode]
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  let tgtDoc =
        withSelfClassifiedCtors
          [(mode, [])]
          Doctrine
            { dName = "TgtMissingCtor"
            , dModes = mkModes [mode]
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  srcDoc' <- case validateDoctrineNormalized srcDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure srcDoc
  tgtDoc' <- case validateDoctrineNormalized tgtDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure tgtDoc
  let mor =
        Morphism
          { morName = "MissingCtor"
          , morSrc = srcDoc'
          , morTgt = tgtDoc'
          , morIsCoercion = False
          , morModeMap = identityModeMap srcDoc'
          , morModMap = identityModMap srcDoc'
          , morAttrSortMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckNone
          , morPolicy = UseAllOriented
          }
  case applyMorphismTyNormalized mor (tcon mode "T" []) of
    Left err -> assertBool "expected strict mapped-constructor failure" ("missing mapped constructor" `T.isInfixOf` err)
    Right _ -> assertFailure "expected applyMorphismTy to fail when mapped constructor is missing in target"

testMorphismRequiresExplicitComprehensionMappings :: Assertion
testMorphismRequiresExplicitComprehensionMappings = do
  let mode = ModeName "M"
  let srcDoc =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = "SrcCompStrict"
            , dModes = mkModes [mode]
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  let tgtDoc =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = "TgtCompStrict"
            , dModes = mkModes [mode]
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  srcDoc' <- case validateDoctrineNormalized srcDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure srcDoc
  tgtDoc' <- case validateDoctrineNormalized tgtDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure tgtDoc
  let mor =
        Morphism
          { morName = "CompStrict"
          , morSrc = srcDoc'
          , morTgt = tgtDoc'
          , morIsCoercion = False
          , morModeMap = identityModeMap srcDoc'
          , morModMap = identityModMap srcDoc'
          , morAttrSortMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morCheck = CheckNone
          , morPolicy = UseAllOriented
          }
  srcDiag <- either (assertFailure . T.unpack) pure (genD mode [universeObj mode] [universeObj mode] compCtxExtName)
  case applyMorphismDiagramNormalized mor srcDiag of
    Left err -> assertBool "expected missing generator mapping for comprehension support gen" ("missing generator mapping" `T.isInfixOf` err)
    Right _ -> assertFailure "expected explicit comprehension support generator mapping to be required"

testMorphismInstantiationSubstFailure :: Assertion
testMorphismInstantiationSubstFailure = do
  let mode = ModeName "M"
  let aRef = ObjRef mode (ObjName "A")
  let aTy = mkCon aRef []
  let srcGen =
        GenDecl
          { gdName = GenName "f"
          , gdMode = mode
          , gdParams = []
          , gdDom = map InPort [aTy]
          , gdCod = [aTy]
          , gdAttrs = []
          }
  let tgtGen =
        GenDecl
          { gdName = GenName "g"
          , gdMode = mode
          , gdParams = []
          , gdDom = map InPort [aTy]
          , gdCod = [aTy]
          , gdAttrs = []
          }
  let srcDoc =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = "SrcSubstFail"
            , dModes = mkModes [mode]
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.fromList [(mode, M.fromList [(GenName "f", srcGen)])]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  let tgtDoc =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", [])])]
          Doctrine
            { dName = "TgtSubstFail"
            , dModes = mkModes [mode]
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.fromList [(mode, M.fromList [(GenName "g", tgtGen)])]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  src <- case validateDoctrineNormalized srcDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure srcDoc
  tgt <- case validateDoctrineNormalized tgtDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure tgtDoc
  srcDiag <- either (assertFailure . T.unpack) pure (genD mode [aTy] [aTy] (GenName "f"))
  let badTy = mkCon (ObjRef mode (ObjName "Bad")) [OAObj aTy]
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
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case applyMorphismDiagramNormalized mor srcDiag of
    Left _ -> pure ()
    Right _ -> assertFailure "expected applyMorphismDiagram to fail on substitution error"

testBinderIdentityMorphismPreservesBinders :: Assertion
testBinderIdentityMorphismPreservesBinders = do
  let mode = ModeName "M"
  let lamName = GenName "lam"
  let aTy' = mkCon (ObjRef mode (ObjName "A")) []
  let slotSig = BinderSig { bsTmCtx = [], bsDom = [aTy'], bsCod = [aTy'] }
  let lamGen =
        GenDecl
          { gdName = lamName
          , gdMode = mode
          , gdParams = []
          , gdDom = [InBinder slotSig]
          , gdCod = [aTy']
          , gdAttrs = []
          }
  let doc =
        attachComprehensionFixture mode aTy' $
          withSelfClassifiedCtors
            [(mode, [(ObjName "A", [])])]
            Doctrine
              { dName = "LamDoc"
              , dModes = mkModes [mode]
              , dAcyclicModes = S.empty
              , dAttrSorts = M.empty
              , dGens = M.fromList [(mode, M.fromList [(lamName, lamGen)])]
              , dCells2 = []
              , dActions = M.empty
              , dObligations = []
              }
  doc' <- case validateDoctrineNormalized doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure doc
  let body = idD mode [aTy']
  srcDiag0 <- either (assertFailure . T.unpack) pure (genD mode [] [aTy'] lamName)
  srcDiag <- either (assertFailure . T.unpack) pure (setSingleEdgeBargs srcDiag0 [BAConcrete body])
  img0 <- either (assertFailure . T.unpack) pure (genD mode [] [aTy'] lamName)
  let hole = BinderMetaVar "b0"
  img <- either (assertFailure . T.unpack) pure (setSingleEdgeBargs img0 [BAMeta hole])
  compImgs <- either (assertFailure . T.unpack) pure (compIdentityImages mode aTy')
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
          , morGenMap = M.fromList ([((mode, lamName), GenImage img (M.fromList [(hole, slotSig)]))] <> compImgs)
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case checkMorphismNormalized mor of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  mapped <- case applyMorphismDiagramNormalized mor srcDiag of
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
  let aTy' = mkCon (ObjRef mode (ObjName "A")) []
  let slotSig = BinderSig { bsTmCtx = [], bsDom = [aTy'], bsCod = [aTy'] }
  let gDecl =
        GenDecl
          { gdName = gName
          , gdMode = mode
          , gdParams = []
          , gdDom = [InPort aTy', InBinder slotSig]
          , gdCod = [aTy']
          , gdAttrs = []
          }
  let doc =
        attachComprehensionFixture mode aTy' $
          withSelfClassifiedCtors
            [(mode, [(ObjName "A", [])])]
            Doctrine
              { dName = "SpliceMetaDoc"
              , dModes = mkModes [mode]
              , dAcyclicModes = S.empty
              , dAttrSorts = M.empty
              , dGens = M.fromList [(mode, M.fromList [(gName, gDecl)])]
              , dCells2 = []
              , dActions = M.empty
              , dObligations = []
              }
  doc' <- case validateDoctrineNormalized doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure doc
  let xMeta = BinderMetaVar "X"
  let b0 = BinderMetaVar "b0"
  srcDiag0 <- either (assertFailure . T.unpack) pure (genD mode [aTy'] [aTy'] gName)
  srcDiag <- either (assertFailure . T.unpack) pure (setSingleEdgeBargs srcDiag0 [BAMeta xMeta])
  img0 <- either (assertFailure . T.unpack) pure (genD mode [aTy'] [aTy'] (GenName "tmp"))
  img <- either (assertFailure . T.unpack) pure (setSingleEdgePayload img0 (PSplice b0))
  compImgs <- either (assertFailure . T.unpack) pure (compIdentityImages mode aTy')
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
          , morGenMap = M.fromList ([((mode, gName), GenImage img (M.fromList [(b0, slotSig)]))] <> compImgs)
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case checkMorphismNormalized mor of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  mapped <- case applyMorphismDiagramNormalized mor srcDiag of
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
  let aTy' = mkCon (ObjRef mode (ObjName "A")) []
  let slotSig = BinderSig { bsTmCtx = [], bsDom = [aTy'], bsCod = [aTy'] }
  let wrongSig = BinderSig { bsTmCtx = [], bsDom = [], bsCod = [aTy'] }
  let lamGen =
        GenDecl
          { gdName = lamName
          , gdMode = mode
          , gdParams = []
          , gdDom = [InBinder slotSig]
          , gdCod = [aTy']
          , gdAttrs = []
          }
  let doc =
        attachComprehensionFixture mode aTy' $
          withSelfClassifiedCtors
            [(mode, [(ObjName "A", [])])]
            Doctrine
              { dName = "BadBinderSigsDoc"
              , dModes = mkModes [mode]
              , dAcyclicModes = S.empty
              , dAttrSorts = M.empty
              , dGens = M.fromList [(mode, M.fromList [(lamName, lamGen)])]
              , dCells2 = []
              , dActions = M.empty
              , dObligations = []
              }
  doc' <- case validateDoctrineNormalized doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure doc
  let hole = BinderMetaVar "b0"
  img0 <- either (assertFailure . T.unpack) pure (genD mode [] [aTy'] lamName)
  img <- either (assertFailure . T.unpack) pure (setSingleEdgeBargs img0 [BAMeta hole])
  compImgs <- either (assertFailure . T.unpack) pure (compIdentityImages mode aTy')
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
          , morGenMap = M.fromList ([((mode, lamName), GenImage img (M.fromList [(hole, wrongSig)]))] <> compImgs)
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case checkMorphismNormalized mor of
    Left err ->
      assertBool
        "expected binder-hole signature mismatch"
        ("binder-hole signatures mismatch" `T.isInfixOf` err)
    Right () ->
      assertFailure "expected checkMorphism to reject incorrect binder-hole signatures"

testTypeTemplateCycleRejected :: Assertion
testTypeTemplateCycleRejected = do
  let mode = ModeName "M"
  let aRef = ObjRef mode (ObjName "A")
  let bRef = ObjRef mode (ObjName "B")
  let doc =
        withSelfClassifiedCtors
          [(mode, [(ObjName "A", []), (ObjName "B", [])])]
          Doctrine
            { dName = "CycleDoc"
            , dModes = mkModes [mode]
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  doc' <- case validateDoctrineNormalized doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure doc
  compImgs <- either (assertFailure . T.unpack) pure (compIdentityImages mode (universeObj mode))
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
                [ (aRef, TypeTemplate [] (mkCon bRef []))
                , (bRef, TypeTemplate [] (mkCon aRef []))
                ]
          , morGenMap = M.fromList compImgs
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case checkMorphismNormalized mor of
    Left err ->
      assertBool "expected cyclic type template rejection" ("cyclic type template map" `T.isInfixOf` err)
    Right () ->
      assertFailure "expected checkMorphism to reject cyclic templates"

testTermTemplateSortMismatch :: Assertion
testTermTemplateSortMismatch = do
  let modeM' = ModeName "M"
  let modeI' = ModeName "I"
  let natRef = ObjRef modeI' (ObjName "Nat")
  let boolRef = ObjRef modeI' (ObjName "Bool")
  let vecRef = ObjRef modeM' (ObjName "Vec")
  let natTy = mkCon natRef []
  let boolTy = mkCon boolRef []
  let srcDoc =
        withSelfClassifiedCtors
          [ (modeI', [(ObjName "Nat", []), (ObjName "Bool", [])])
          , (modeM', [(ObjName "Vec", [TPS_Tm natTy, TPS_Ty modeM'])])
          ]
          Doctrine
            { dName = "SrcSortMismatch"
            , dModes = mkModes [modeM', modeI']
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  let tgtDoc =
        withSelfClassifiedCtors
          [ (modeI', [(ObjName "Nat", []), (ObjName "Bool", [])])
          , (modeM', [(ObjName "Vec", [TPS_Tm natTy, TPS_Ty modeM'])])
          ]
          Doctrine
            { dName = "TgtSortMismatch"
            , dModes = mkModes [modeM', modeI']
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.empty
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  src <- case validateDoctrineNormalized srcDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure srcDoc
  tgt <- case validateDoctrineNormalized tgtDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure tgtDoc
  compImgsI <- either (assertFailure . T.unpack) pure (compIdentityImages modeI' (universeObj modeI'))
  compImgsM <- either (assertFailure . T.unpack) pure (compIdentityImages modeM' (universeObj modeM'))
  let nWrong = TmVar { tmvName = "n", tmvSort = boolTy, tmvScope = 0, tmvOwnerMode = Nothing }
  let aVar = mkModeMetaVar "a" modeM'
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
                      [GP_Tm nWrong, GP_Ty (aVar)]
                      (OVar aVar)
                  )
                ]
          , morGenMap = M.fromList (compImgsI <> compImgsM)
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case checkMorphismNormalized mor of
    Left err ->
      assertBool
        "expected term-parameter sort mismatch"
        ("term-parameter sort mismatch" `T.isInfixOf` err || "term-parameter sort mismatch" `T.isInfixOf` err)
    Right () ->
      assertFailure "expected checkMorphism to reject term sort mismatch"

testTermTypeTemplateInstantiation :: Assertion
testTermTypeTemplateInstantiation = do
  let modeM' = ModeName "M"
  let modeI' = ModeName "I"
  let natRef = ObjRef modeI' (ObjName "Nat")
  let aRef = ObjRef modeM' (ObjName "A")
  let vecRef = ObjRef modeM' (ObjName "Vec")
  let vec2Ref = ObjRef modeM' (ObjName "Vec2")
  let natTy = mkCon natRef []
  let aTy' = mkCon aRef []
  let z = TMFun (GenName "Z") []
  let s x = TMFun (GenName "S") [x]
  let zGen =
        GenDecl
          { gdName = GenName "Z"
          , gdMode = modeI'
          , gdParams = []
          , gdDom = []
          , gdCod = [natTy]
          , gdAttrs = []
          }
  let sGen =
        GenDecl
          { gdName = GenName "S"
          , gdMode = modeI'
          , gdParams = []
          , gdDom = [InPort natTy]
          , gdCod = [natTy]
          , gdAttrs = []
          }
  let natCtor =
        GenDecl
          { gdName = GenName "Nat"
          , gdMode = modeI'
          , gdParams = []
          , gdDom = []
          , gdCod = [universeObj modeI']
          , gdAttrs = []
          }
  let aCtor =
        GenDecl
          { gdName = GenName "A"
          , gdMode = modeM'
          , gdParams = []
          , gdDom = []
          , gdCod = [universeObj modeM']
          , gdAttrs = []
          }
  let nIx = TmVar { tmvName = "n_ix", tmvSort = natTy, tmvScope = -1, tmvOwnerMode = Nothing }
  let aIx = TmVar { tmvName = "a_ix", tmvSort = universeObj modeM', tmvScope = 1, tmvOwnerMode = Just modeM' }
  let vecCtor =
        GenDecl
          { gdName = GenName "Vec"
          , gdMode = modeM'
          , gdParams = [GP_Tm nIx, GP_Ty aIx]
          , gdDom = []
          , gdCod = [universeObj modeM']
          , gdAttrs = []
          }
  let vec2Ctor =
        GenDecl
          { gdName = GenName "Vec2"
          , gdMode = modeM'
          , gdParams = [GP_Tm nIx, GP_Ty aIx]
          , gdDom = []
          , gdCod = [universeObj modeM']
          , gdAttrs = []
          }
  let srcDoc =
        Doctrine
          { dName = "SrcTermTemplate"
          , dModes = selfClassifiedModes [modeM', modeI']
          , dAcyclicModes = S.empty
          , dAttrSorts = M.empty
          , dGens =
              insertCompSupportGens modeI' $
                insertCompSupportGens modeM' $
                  M.fromList
                    [ (modeI', M.fromList [(gdName natCtor, natCtor), (GenName "Z", zGen), (GenName "S", sGen)])
                    , (modeM', M.fromList [(gdName aCtor, aCtor), (gdName vecCtor, vecCtor)])
                    ]
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
          }
  let tgtDoc =
        Doctrine
          { dName = "TgtTermTemplate"
          , dModes = selfClassifiedModes [modeM', modeI']
          , dAcyclicModes = S.empty
          , dAttrSorts = M.empty
          , dGens =
              insertCompSupportGens modeI' $
                insertCompSupportGens modeM' $
                  M.fromList
                    [ (modeI', M.fromList [(gdName natCtor, natCtor), (GenName "Z", zGen), (GenName "S", sGen)])
                    , (modeM', M.fromList [(gdName aCtor, aCtor), (gdName vec2Ctor, vec2Ctor)])
                    ]
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
          }
  src <- case validateDoctrineNormalized srcDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure srcDoc
  tgt <- case validateDoctrineNormalized tgtDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure tgtDoc
  ttSrc <- case doctrineTypeTheory src of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right tt -> pure tt
  let nVar = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 0, tmvOwnerMode = Nothing }
  let aVar = TmVar { tmvName = "a", tmvSort = universeObj modeM', tmvScope = 0, tmvOwnerMode = Just modeM' }
  nSucc <- case termExprToDiagram ttSrc [] natTy (s (TMMeta nVar [])) of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right tm -> pure tm
  zTm <- case termExprToDiagram ttSrc [] natTy z of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right tm -> pure tm
  szTm <- case termExprToDiagram ttSrc [] natTy (s z) of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right tm -> pure tm
  zImg <- case genD modeI' [] [natTy] (GenName "Z") of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  sImg <- case genD modeI' [natTy] [natTy] (GenName "S") of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  compImgsI <- either (assertFailure . T.unpack) pure (compIdentityImages modeI' (universeObj modeI'))
  compImgsM <- either (assertFailure . T.unpack) pure (compIdentityImages modeM' (universeObj modeM'))
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
                      [GP_Tm nVar, GP_Ty aVar]
                      (mkCon vec2Ref [OATm nSucc, OAObj (OVar (aVar))])
                  )
                ]
          , morGenMap =
              M.fromList
                ( [ ((modeI', GenName "Z"), plainImage zImg)
                  , ((modeI', GenName "S"), plainImage sImg)
                  ]
                    <> compImgsI
                    <> compImgsM
                )
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case checkMorphismNormalized mor of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  let srcDiag = idD modeM' [mkCon vecRef [OATm zTm, OAObj aTy']]
  tgtDiag <- case applyMorphismDiagramNormalized mor srcDiag of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  dom <- case diagramDom tgtDiag of
    Left err -> assertFailure (T.unpack err)
    Right ctx -> pure ctx
  case dom of
    [OCon ref [OATm gotTm, OAObj gotA]] -> do
      ref @?= vec2Ref
      gotA @?= aTy'
      gotExpr <- case diagramToTermExpr ttSrc [] natTy gotTm of
        Left err -> assertFailure (T.unpack err) >> fail "unreachable"
        Right e -> pure e
      wantExpr <- case diagramToTermExpr ttSrc [] natTy szTm of
        Left err -> assertFailure (T.unpack err) >> fail "unreachable"
        Right e -> pure e
      gotExpr @?= wantExpr
    _ -> assertFailure "unexpected mapped domain shape"

testTermTemplateKindMismatch :: Assertion
testTermTemplateKindMismatch = do
  let modeM' = ModeName "M"
  let modeI' = ModeName "I"
  let natRef = ObjRef modeI' (ObjName "Nat")
  let vecRef = ObjRef modeM' (ObjName "Vec")
  let vec2Ref = ObjRef modeM' (ObjName "Vec2")
  let natTy = mkCon natRef []
  let zGen =
        GenDecl
          { gdName = GenName "Z"
          , gdMode = modeI'
          , gdParams = []
          , gdDom = []
          , gdCod = [natTy]
          , gdAttrs = []
          }
  let srcDoc =
        withSelfClassifiedCtors
          [ (modeI', [(ObjName "Nat", [])])
          , (modeM', [(ObjName "Vec", [TPS_Tm natTy, TPS_Ty modeM'])])
          ]
          Doctrine
            { dName = "SrcTermTemplateBad"
            , dModes = mkModes [modeM', modeI']
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.fromList [(modeI', M.fromList [(GenName "Z", zGen)])]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  let tgtDoc =
        withSelfClassifiedCtors
          [ (modeI', [(ObjName "Nat", [])])
          , (modeM', [(ObjName "Vec2", [TPS_Tm natTy, TPS_Ty modeM'])])
          ]
          Doctrine
            { dName = "TgtTermTemplateBad"
            , dModes = mkModes [modeM', modeI']
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.fromList [(modeI', M.fromList [(GenName "Z", zGen)])]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  src <- case validateDoctrineNormalized srcDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure srcDoc
  tgt <- case validateDoctrineNormalized tgtDoc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure tgtDoc
  compImgsI <- either (assertFailure . T.unpack) pure (compIdentityImages modeI' (universeObj modeI'))
  compImgsM <- either (assertFailure . T.unpack) pure (compIdentityImages modeM' (universeObj modeM'))
  let nVar = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 0, tmvOwnerMode = Nothing }
  let aVar = mkModeMetaVar "a" modeM'
  let nVarTm = tmMeta nVar
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
                      [GP_Ty (aVar), GP_Tm nVar]
                      (mkCon vec2Ref [OATm nVarTm, OAObj (OVar aVar)])
                  )
                ]
          , morGenMap = M.fromList (compImgsI <> compImgsM)
        , morCheck = CheckAll
          , morPolicy = UseAllOriented
          }
  case checkMorphismNormalized mor of
    Left err ->
      assertBool "expected template kind mismatch" ("kind mismatch" `T.isInfixOf` err)
    Right () ->
      assertFailure "expected morphism check to fail"

testMorphismMapsStructuredTermArgs :: Assertion
testMorphismMapsStructuredTermArgs = do
  let modeM' = ModeName "M"
  let modeI' = ModeName "I"
  let natRef = ObjRef modeI' (ObjName "Nat")
  let vecRef = ObjRef modeM' (ObjName "Vec")
  let natTy = mkCon natRef []
  let succName = GenName "succ"
  let dblName = GenName "dbl"
  let succDecl =
        GenDecl
          { gdName = succName
          , gdMode = modeI'
          , gdParams = []
          , gdDom = [InPort natTy]
          , gdCod = [natTy]
          , gdAttrs = []
          }
  let dblDecl = succDecl { gdName = dblName }
  let srcDoc =
        withSelfClassifiedCtors
          [ (modeI', [(ObjName "Nat", [])])
          , (modeM', [(ObjName "Vec", [TPS_Tm natTy])])
          ]
          Doctrine
            { dName = "SrcStructuredTm"
            , dModes = mkModes [modeM', modeI']
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.fromList [(modeI', M.fromList [(succName, succDecl)])]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  let tgtDoc =
        withSelfClassifiedCtors
          [ (modeI', [(ObjName "Nat", [])])
          , (modeM', [(ObjName "Vec", [TPS_Tm natTy])])
          ]
          Doctrine
            { dName = "TgtStructuredTm"
            , dModes = mkModes [modeM', modeI']
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.fromList [(modeI', M.fromList [(dblName, dblDecl)])]
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  src <- case validateDoctrineNormalized srcDoc of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right () -> pure srcDoc
  tgt <- case validateDoctrineNormalized tgtDoc of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right () -> pure tgtDoc
  dblImg <- case genD modeI' [natTy] [natTy] dblName of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  let mor =
        Morphism
          { morName = "MapSuccToDbl"
          , morSrc = src
          , morTgt = tgt
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morAttrSortMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.fromList [((modeI', succName), plainImage dblImg)]
          , morCheck = CheckNone
          , morPolicy = UseAllOriented
          }
  ttSrc <- case doctrineTypeTheory src of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right tt -> pure tt
  ttTgt <- case doctrineTypeTheory tgt of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right tt -> pure tt
  let nVar = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 0, tmvOwnerMode = Nothing }
  tmSrc <- case termExprToDiagram ttSrc [] natTy (TMFun (GenName "succ") [TMMeta nVar []]) of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right tm -> pure tm
  let tySrc = mkCon vecRef [OATm tmSrc]
  tyTgt <- case applyMorphismTyNormalized mor tySrc of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right ty -> pure ty
  case tyTgt of
    OCon ref [OATm tmOut] -> do
      ref @?= vecRef
      tmExpr <- case diagramToTermExpr ttTgt [] natTy tmOut of
        Left err -> assertFailure (T.unpack err) >> fail "unreachable"
        Right e -> pure e
      tmExpr @?= TMFun (GenName "dbl") [TMMeta nVar []]
    _ ->
      assertFailure "expected mapped Vec term argument"

testMorphismWeakenImageTmCtx :: Assertion
testMorphismWeakenImageTmCtx = do
  let mode = ModeName "M"
  let tyX = mkCon (ObjRef mode (ObjName "X")) []
  let srcName = GenName "g"
  let tgtName = GenName "h"
  let mkGen name =
        GenDecl
          { gdName = name
          , gdMode = mode
          , gdParams = []
          , gdDom = [InPort tyX]
          , gdCod = [tyX]
          , gdAttrs = []
          }
  let srcDoc =
        withSelfClassifiedCtors
          [(mode, [(ObjName "X", [])])]
          Doctrine
            { dName = "SrcWeakenMorph"
            , dModes = mkModes [mode]
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.singleton mode (M.singleton srcName (mkGen srcName))
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  let tgtDoc =
        withSelfClassifiedCtors
          [(mode, [(ObjName "X", [])])]
          Doctrine
            { dName = "TgtWeakenMorph"
            , dModes = mkModes [mode]
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = M.singleton mode (M.singleton tgtName (mkGen tgtName))
            , dCells2 = []
            , dActions = M.empty
            , dObligations = []
            }
  src <- case validateDoctrineNormalized srcDoc of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right () -> pure srcDoc
  tgt <- case validateDoctrineNormalized tgtDoc of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right () -> pure tgtDoc
  img <- case genD mode [tyX] [tyX] tgtName of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  let mor =
        Morphism
          { morName = "WeakenMorph"
          , morSrc = src
          , morTgt = tgt
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morAttrSortMap = M.empty
          , morTypeMap = M.empty
          , morGenMap = M.singleton (mode, srcName) (plainImage img)
          , morCheck = CheckNone
          , morPolicy = UseAllOriented
          }
  srcDiag <- case genDTm mode [tyX] [tyX] [tyX] srcName of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  mapped <- case applyMorphismDiagramNormalized mor srcDiag of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  dTmCtx mapped @?= [tyX]

modeM :: ModeName
modeM = ModeName "M"

aTy :: Obj
aTy = mkCon (ObjRef modeM (ObjName "A")) []

strTy :: Obj
strTy = mkCon (ObjRef modeM (ObjName "Str")) []

mkMonoid :: Either Text Doctrine
mkMonoid = do
  let mt = mkModes [modeM]
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
                      , gdParams = []
                      , gdDom = map InPort []
                      , gdCod = [aTy]
                      , gdAttrs = []
                      }
                  )
                , ( GenName "mul"
                  , GenDecl
                      { gdName = GenName "mul"
                      , gdMode = modeM
                      , gdParams = []
                      , gdDom = map InPort [aTy, aTy]
                      , gdCod = [aTy]
                      , gdAttrs = []
                      }
                  )
                ]
            )
          ]
  let doc =
        withSelfClassifiedCtors
          [(modeM, [(ObjName "A", [])])]
          Doctrine
            { dName = "Monoid"
            , dModes = mt
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = gens
            , dCells2 = [assoc { c2Class = Structural }, unitL, unitR]
            , dActions = M.empty
            , dObligations = []
            }
  case validateDoctrineNormalized doc of
    Left err -> Left err
    Right () -> Right doc

mkStringMonoid :: Either Text Doctrine
mkStringMonoid = do
  let mt = mkModes [modeM]
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
                      , gdParams = []
                      , gdDom = map InPort []
                      , gdCod = [strTy]
                      , gdAttrs = []
                      }
                  )
                , ( GenName "append"
                  , GenDecl
                      { gdName = GenName "append"
                      , gdMode = modeM
                      , gdParams = []
                      , gdDom = map InPort [strTy, strTy]
                      , gdCod = [strTy]
                      , gdAttrs = []
                      }
                  )
                ]
            )
          ]
  let doc =
        withSelfClassifiedCtors
          [(modeM, [(ObjName "Str", [])])]
          Doctrine
            { dName = "StringMonoid"
            , dModes = mt
            , dAcyclicModes = S.empty
            , dAttrSorts = M.empty
            , dGens = gens
            , dCells2 = [assoc { c2Class = Structural }, unitL, unitR]
            , dActions = M.empty
            , dObligations = []
            }
  case validateDoctrineNormalized doc of
    Left err -> Left err
    Right () -> Right doc

assocRule :: Text -> Obj -> GenName -> Either Text Cell2
assocRule name ty mulName = do
  mul <- genD modeM [ty, ty] [ty] mulName
  id1 <- pure (idD modeM [ty])
  left <- tensorD mul id1
  lhs <- compD (modeOnlyTypeTheory (mkModes [modeM])) mul left
  right <- tensorD id1 mul
  rhs <- compD (modeOnlyTypeTheory (mkModes [modeM])) mul right
  pure Cell2
    { c2Name = name
    , c2Class = Computational
    , c2Orient = LR
    , c2Params = []
    , c2LHS = lhs
    , c2RHS = rhs
    }

unitRule :: Text -> Obj -> GenName -> GenName -> Bool -> Either Text Cell2
unitRule name ty unitName mulName leftSide = do
  unit <- genD modeM [] [ty] unitName
  mul <- genD modeM [ty, ty] [ty] mulName
  id1 <- pure (idD modeM [ty])
  expr <-
    if leftSide
      then do
        tens <- tensorD unit id1
        compD (modeOnlyTypeTheory (mkModes [modeM])) mul tens
      else do
        tens <- tensorD id1 unit
        compD (modeOnlyTypeTheory (mkModes [modeM])) mul tens
  pure Cell2
    { c2Name = name
    , c2Class = Computational
    , c2Orient = LR
    , c2Params = []
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

testMorphismRejectsClassifierEdgeMismatch :: Assertion
testMorphismRejectsClassifierEdgeMismatch =
  case elabProgram morphismClassifierMismatchProgram of
    Left err ->
      if "classifier edge mismatch" `T.isInfixOf` err || "is not classified in target" `T.isInfixOf` err
        then pure ()
        else assertFailure ("unexpected morphism classifier-mismatch error: " <> T.unpack err)
    Right _ ->
      assertFailure "expected morphism elaboration to reject classifier-edge mismatch"

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
    <> "  mode M classifiedBy M via U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [U_M] @M;\n"
    <> "  gen B : [] -> [U_M] @M;\n"
    <> "  gen f : [B] -> [B] @M;\n"
    <> "  rule computational f_id -> : [B] -> [B] @M =\n"
    <> "    f == id[B]\n"
    <> "}\n"
    <> "doctrine T where {\n"
    <> "  mode M classifiedBy M via U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [U_M] @M;\n"
    <> "  gen B : [] -> [U_M] @M;\n"
    <> "  gen g : [B] -> [B] @M;\n"
    <> "}\n"
    <> "morphism m : S -> T where {\n"
    <> "  check all;\n"
    <> "  mode M -> M;\n"
    <> "  gen comp_ctx_ext @M -> comp_ctx_ext\n"
    <> "  gen comp_var @M -> comp_var\n"
    <> "  gen comp_reindex @M -> comp_reindex\n"
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
    <> "  mode M classifiedBy M via U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [U_M] @M;\n"
    <> "  gen B : [] -> [U_M] @M;\n"
    <> "  gen and : [B, B] -> [B] @M;\n"
    <> "}\n"
    <> "doctrine T where {\n"
    <> "  mode M classifiedBy M via U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [U_M] @M;\n"
    <> "  gen B : [] -> [U_M] @M;\n"
    <> "  gen true : [] -> [B] @M;\n"
    <> "}\n"
    <> "morphism bad : S -> T where {\n"
    <> "  check none;\n"
    <> "  mode M -> M;\n"
    <> "  gen comp_ctx_ext @M -> comp_ctx_ext\n"
    <> "  gen comp_var @M -> comp_var\n"
    <> "  gen comp_reindex @M -> comp_reindex\n"
    <> "  gen and @M -> true\n"
    <> "}\n"

morphismClassifierMismatchProgram :: Text
morphismClassifierMismatchProgram =
  "doctrine S where {\n"
    <> "  mode Ty classifiedBy Ty via U_Ty;\n"
    <> "  gen comp_ctx_ext(a@Ty) : [a] -> [a] @Ty;\n"
    <> "  gen comp_var(a@Ty) : [a] -> [a] @Ty;\n"
    <> "  gen comp_reindex(a@Ty) : [a] -> [a] @Ty;\n"
    <> "  comprehension Ty where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_Ty : [] -> [U_Ty] @Ty;\n"
    <> "  gen U : [] -> [U_Ty] @Ty;\n"
    <> "  mode Tm classifiedBy Ty via U;\n"
    <> "  gen t_ctx_ext(a@Tm) : [a] -> [a] @Tm;\n"
    <> "  gen t_var(a@Tm) : [a] -> [a] @Tm;\n"
    <> "  gen t_reindex(a@Tm) : [a] -> [a] @Tm;\n"
    <> "  comprehension Tm where { ctx_ext = t_ctx_ext; var = t_var; reindex = t_reindex; };\n"
    <> "}\n"
    <> "doctrine T where {\n"
    <> "  mode Ty2 classifiedBy Ty2 via U_Ty2;\n"
    <> "  gen comp_ctx_ext(a@Ty2) : [a] -> [a] @Ty2;\n"
    <> "  gen comp_var(a@Ty2) : [a] -> [a] @Ty2;\n"
    <> "  gen comp_reindex(a@Ty2) : [a] -> [a] @Ty2;\n"
    <> "  comprehension Ty2 where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_Ty2 : [] -> [U_Ty2] @Ty2;\n"
    <> "  mode Tm2 classifiedBy Tm2 via U_Tm2;\n"
    <> "  gen t_ctx_ext(a@Tm2) : [a] -> [a] @Tm2;\n"
    <> "  gen t_var(a@Tm2) : [a] -> [a] @Tm2;\n"
    <> "  gen t_reindex(a@Tm2) : [a] -> [a] @Tm2;\n"
    <> "  comprehension Tm2 where { ctx_ext = t_ctx_ext; var = t_var; reindex = t_reindex; };\n"
    <> "  gen U_Tm2 : [] -> [U_Tm2] @Tm2;\n"
    <> "}\n"
    <> "morphism bad : S -> T where {\n"
    <> "  check none;\n"
    <> "  mode Ty -> Ty2;\n"
    <> "  mode Tm -> Tm2;\n"
    <> "  type U @Ty -> U_Ty2 @Ty2;\n"
    <> "  gen comp_ctx_ext @Ty -> comp_ctx_ext\n"
    <> "  gen comp_var @Ty -> comp_var\n"
    <> "  gen comp_reindex @Ty -> comp_reindex\n"
    <> "  gen t_ctx_ext @Tm -> t_ctx_ext\n"
    <> "  gen t_var @Tm -> t_var\n"
    <> "  gen t_reindex @Tm -> t_reindex\n"
    <> "}\n"

wireMetaRuleProgram :: Text
wireMetaRuleProgram =
  "doctrine D where {\n"
    <> "  mode M classifiedBy M via U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [U_M] @M;\n"
    <> "  gen B : [] -> [U_M] @M;\n"
    <> "  gen true : [] -> [B] @M;\n"
    <> "  gen and : [B, B] -> [B] @M;\n"
    <> "  rule computational and_true_r -> : [B] -> [B] @M =\n"
    <> "    (true * ?x) ; and == ?x\n"
    <> "}\n"

wireMetaDuplicateProgram :: Text
wireMetaDuplicateProgram =
  "doctrine D where {\n"
    <> "  mode M classifiedBy M via U_M;\n"
    <> "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_var(a@M) : [a] -> [a] @M;\n"
    <> "  gen comp_reindex(a@M) : [a] -> [a] @M;\n"
    <> "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };\n"
    <> "  gen U_M : [] -> [U_M] @M;\n"
    <> "  gen B : [] -> [U_M] @M;\n"
    <> "  gen true : [] -> [B] @M;\n"
    <> "  gen and : [B, B] -> [B] @M;\n"
    <> "  rule computational and_bad -> : [B] -> [B] @M =\n"
    <> "    (true * ?x) ; and == (?x * ?x) ; and\n"
    <> "}\n"
