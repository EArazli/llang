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
import Strat.Common.Rules (RewritePolicy(..), RuleClass(..), Orientation(..))
import Strat.Poly.ModeTheory
import Strat.Poly.TypeExpr
import Strat.Poly.Names
import Strat.Poly.Diagram
import Strat.Poly.Graph (Edge(..), EdgePayload(..))
import Strat.Poly.Cell2
import Strat.Poly.Doctrine
import Strat.Poly.Morphism
import Test.Poly.Helpers (mkModes, identityModeMap, identityModMap)


tests :: TestTree
tests =
  testGroup
    "Poly.Morphism"
    [ testCase "monoid morphism to string monoid" testMonoidMorphism
    , testCase "type map can reorder parameters" testTypeMapReorder
    , testCase "cross-mode morphism applies mode map" testCrossModeMorphism
    , testCase "modality map rewrites modality applications in types" testModalityMapRewritesTypeModalities
    ]

tvar :: ModeName -> Text -> TyVar
tvar mode name = TyVar { tvName = name, tvMode = mode }

tcon :: ModeName -> Text -> [TypeExpr] -> TypeExpr
tcon mode name args = TCon (TypeRef mode (TypeName name)) args

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
        , morGenMap = M.fromList [((modeM, GenName "unit"), unitImg), ((modeM, GenName "mul"), mulImg)]
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
  let genSrc = GenDecl genName mode [a, b] [TCon (TypeRef mode prod) [TVar a, TVar b]] [TCon (TypeRef mode prod) [TVar a, TVar b]] []
  let genTgt = GenDecl genName mode [a, b] [TCon (TypeRef mode pair) [TVar a, TVar b]] [TCon (TypeRef mode pair) [TVar a, TVar b]] []
  let docSrc = Doctrine
        { dName = "Src"
        , dModes = mkModes [mode]
        , dAttrSorts = M.empty
        , dTypes = M.fromList [(mode, M.fromList [(prod, TypeSig [mode, mode])])]
        , dGens = M.fromList [(mode, M.fromList [(genName, genSrc)])]
        , dCells2 = []
        }
  let docTgt = Doctrine
        { dName = "Tgt"
        , dModes = mkModes [mode]
        , dAttrSorts = M.empty
        , dTypes = M.fromList [(mode, M.fromList [(pair, TypeSig [mode, mode])])]
        , dGens = M.fromList [(mode, M.fromList [(genName, genTgt)])]
        , dCells2 = []
        }
  docSrc' <- case validateDoctrine docSrc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docSrc
  docTgt' <- case validateDoctrine docTgt of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure docTgt
  img <- either (assertFailure . T.unpack) pure (genD mode [TCon (TypeRef mode pair) [TVar b, TVar a]] [TCon (TypeRef mode pair) [TVar b, TVar a]] genName)
  let typeMap = M.fromList [(TypeRef mode prod, TypeTemplate [a, b] (TCon (TypeRef mode pair) [TVar b, TVar a]))]
  let mor = Morphism
        { morName = "SwapProd"
        , morSrc = docSrc'
        , morTgt = docTgt'
        , morIsCoercion = False
        , morModeMap = identityModeMap docSrc'
        , morModMap = identityModMap docSrc'
        , morAttrSortMap = M.empty
        , morTypeMap = typeMap
        , morGenMap = M.fromList [((mode, genName), img)]
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
  let fGen = GenDecl (GenName "f") modeC [] [aTy] [aTy] []
  let gGen = GenDecl (GenName "g") modeV [] [bTy] [bTy] []
  let docSrc = Doctrine
        { dName = "Src"
        , dModes = mkModes [modeC]
        , dAttrSorts = M.empty
        , dTypes = M.fromList [(modeC, M.fromList [(TypeName "A", TypeSig [])])]
        , dGens = M.fromList [(modeC, M.fromList [(GenName "f", fGen)])]
        , dCells2 = []
        }
  let docTgt = Doctrine
        { dName = "Tgt"
        , dModes = mkModes [modeV]
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
        , morGenMap = M.fromList [((modeC, GenName "f"), img)]
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
  let genGSrc = GenDecl (GenName "g") modeB [] [fBaseSrc] [fBaseSrc] []
  let genGGSrc = GenDecl (GenName "gg") modeB [] [hfBaseSrc] [hfBaseSrc] []
  let genGTgt = GenDecl (GenName "g") modeD [] [gBaseTgt] [gBaseTgt] []
  let genGGTgt = GenDecl (GenName "gg") modeD [] [kgBaseTgt] [kgBaseTgt] []
  let docSrc = Doctrine
        { dName = "SrcModal"
        , dModes = modeTheorySrc
        , dAttrSorts = M.empty
        , dTypes = M.fromList [(modeA, M.fromList [(TypeName "Base", TypeSig [])])]
        , dGens = M.fromList [(modeB, M.fromList [(GenName "g", genGSrc), (GenName "gg", genGGSrc)])]
        , dCells2 = []
        }
  let docTgt = Doctrine
        { dName = "TgtModal"
        , dModes = modeTheoryTgt
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
        , morGenMap = M.fromList [((modeB, GenName "g"), imgG), ((modeB, GenName "gg"), imgGG)]
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
        [Edge _ (PGen genName attrs) _ _] -> do
          genName @?= GenName name
          attrs @?= M.empty
        _ -> assertFailure "expected exactly one generator edge"

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
                [ (GenName "unit", GenDecl (GenName "unit") modeM [] [] [aTy] [])
                , (GenName "mul", GenDecl (GenName "mul") modeM [] [aTy, aTy] [aTy] [])
                ]
            )
          ]
  let doc = Doctrine
        { dName = "Monoid"
        , dModes = mt
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
                [ (GenName "empty", GenDecl (GenName "empty") modeM [] [] [strTy] [])
                , (GenName "append", GenDecl (GenName "append") modeM [] [strTy, strTy] [strTy] [])
                ]
            )
          ]
  let doc = Doctrine
        { dName = "StringMonoid"
        , dModes = mt
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
  lhs <- compD (mkModes [modeM]) mul left
  right <- tensorD id1 mul
  rhs <- compD (mkModes [modeM]) mul right
  pure Cell2
    { c2Name = name
    , c2Class = Computational
    , c2Orient = LR
    , c2TyVars = []
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
        compD (mkModes [modeM]) mul tens
      else do
        tens <- tensorD id1 unit
        compD (mkModes [modeM]) mul tens
  pure Cell2
    { c2Name = name
    , c2Class = Computational
    , c2Orient = LR
    , c2TyVars = []
    , c2LHS = expr
    , c2RHS = id1
    }
