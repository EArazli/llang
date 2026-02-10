{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Pushout
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName(..), ModName(..), ModExpr(..), ModDecl(..), ModEqn(..), ModeTheory(..), ModeInfo(..), VarDiscipline(..), mtModes, mtDecls)
import Strat.Poly.TypeExpr (TyVar(..), TypeName(..), TypeRef(..), TypeExpr(..), TypeArg(..), IxVar(..), IxTerm(..))
import Strat.Poly.IndexTheory (IxTheory(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram (genD, idD)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..), ParamSig(..), InputShape(..), gdPlainDom, validateDoctrine)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Morphism (Morphism(..), TemplateParam(..), TypeTemplate(..), applyMorphismDiagram)
import Strat.Poly.Pushout (computePolyPushout, PolyPushoutResult(..))
import Strat.Poly.Graph (diagramIsoEq)
import Strat.Common.Rules (RuleClass(..), Orientation(..), RewritePolicy(..))


tests :: TestTree
tests =
  testGroup
    "Poly.Pushout"
    [ testCase "pushout dedups equations by body" testPushoutDedupByBody
    , testCase "pushout type permutation commutes" testPushoutTypePermutationCommutes
    , testCase "pushout merges cell orientations" testPushoutMergeOrient
    , testCase "pushout merges cell classes" testPushoutMergeClass
    , testCase "pushout rejects name conflict with different bodies" testPushoutNameConflict
    , testCase "pushout rejects non-identity mode maps" testPushoutRejectsModeMap
    , testCase "pushout handles alpha-renaming with mode equations" testPushoutAlphaRenameWithModeEq
    , testCase "pushout supports indexed type maps" testPushoutIndexedTypeMaps
    , testCase "pushout merges cells alpha-equivalent over index vars" testPushoutCellIxAlphaEq
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

tvar :: ModeName -> Text -> TyVar
tvar mode name = TyVar { tvName = name, tvMode = mode }

tcon :: ModeName -> Text -> [TypeExpr] -> TypeExpr
tcon mode name args = TCon (TypeRef mode (TypeName name)) (map TAType args)

identityModeMap :: Doctrine -> M.Map ModeName ModeName
identityModeMap doc =
  M.fromList [ (m, m) | m <- M.keys (mtModes (dModes doc)) ]

identityModMap :: Doctrine -> M.Map ModName ModExpr
identityModMap doc =
  M.fromList
    [ (name, ModExpr { meSrc = mdSrc decl, meTgt = mdTgt decl, mePath = [name] })
    | (name, decl) <- M.toList (mtDecls (dModes doc))
    ]

mkModes :: S.Set ModeName -> ModeTheory
mkModes modes =
  ModeTheory
    (M.fromList [ (m, ModeInfo m Linear) | m <- S.toList modes ])
    M.empty
    []
    []


testPushoutDedupByBody :: Assertion
testPushoutDedupByBody = do
  let mode = ModeName "M"
  base <- case mkDoctrine mode "Interface" (tvar mode "a") "eqI" of
    Left err -> assertFailure err
    Right d -> pure d
  left <- case mkDoctrine mode "Left" (tvar mode "a") "eqLeft" of
    Left err -> assertFailure err
    Right d -> pure d
  right <- case mkDoctrine mode "Right" (tvar mode "b") "eqRight" of
    Left err -> assertFailure err
    Right d -> pure d
  let morLeft = mkInclusionMorph "Left.in" base left (tvar mode "a")
  let morRight = mkInclusionMorph "Right.in" base right (tvar mode "b")
  res <- case computePolyPushout "Po" morLeft morRight of
    Left err -> assertFailure (show err)
    Right r -> pure r
  length (dCells2 (poDoctrine res)) @?= 1


mkDoctrine :: ModeName -> Text -> TyVar -> Text -> Either String Doctrine
mkDoctrine mode name tyVar cellName = do
  let gen = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdTyVars = [tyVar]
        , gdIxVars = []
    , gdDom = map InPort [TVar tyVar]
        , gdCod = [TVar tyVar]
        , gdAttrs = []
        }
  lhs <- case genD mode [TVar tyVar] [TVar tyVar] (gdName gen) of
    Left err -> Left (show err)
    Right d -> Right d
  let rhs = idD mode [TVar tyVar]
  let cell = Cell2
        { c2Name = cellName
        , c2Class = Computational
        , c2Orient = LR
        , c2TyVars = [tyVar]
        , c2IxVars = []
        , c2LHS = lhs
        , c2RHS = rhs
        }
  let doc = Doctrine
        { dName = name
        , dModes = mkModes (S.singleton mode)
      , dIndexModes = S.empty
      , dIxTheory = M.empty
        , dTypes = M.empty
        , dGens = M.fromList [(mode, M.fromList [(gdName gen, gen)])]
        , dCells2 = [cell]
        , dAttrSorts = M.empty
        }
  case validateDoctrine doc of
    Left err -> Left (show err)
    Right () -> Right doc

mkInclusionMorph :: Text -> Doctrine -> Doctrine -> TyVar -> Morphism
mkInclusionMorph name src tgt tyVar =
  let mode = ModeName "M"
      diag = case genD mode [TVar tyVar] [TVar tyVar] (GenName "f") of
        Left _ -> error "mkInclusionMorph: genD failed"
        Right d -> d
      genMap = M.fromList [((mode, GenName "f"), diag)]
  in Morphism
      { morName = name
      , morSrc = src
      , morTgt = tgt
      , morIsCoercion = False
      , morModeMap = identityModeMap src
      , morModMap = identityModMap src
      , morTypeMap = M.empty
      , morGenMap = genMap
      , morIxFunMap = M.empty
      , morAttrSortMap = M.empty
      , morPolicy = UseAllOriented
      , morFuel = 10
      }

testPushoutMergeOrient :: Assertion
testPushoutMergeOrient = do
  let mode = ModeName "M"
  base <- require (mkCellDoctrine mode "A" Computational LR)
  left <- require (mkCellDoctrine mode "B" Computational LR)
  right <- require (mkCellDoctrine mode "C" Computational RL)
  let morLeft = mkIdMorph "fLeft" base left
  let morRight = mkIdMorph "fRight" base right
  res <- case computePolyPushout "P" morLeft morRight of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  let cells = dCells2 (poDoctrine res)
  case findCell "eq" cells of
    Nothing -> assertFailure "expected merged cell"
    Just cell ->
      c2Orient cell @?= Bidirectional

testPushoutMergeClass :: Assertion
testPushoutMergeClass = do
  let mode = ModeName "M"
  base <- require (mkCellDoctrine mode "A" Computational LR)
  left <- require (mkCellDoctrine mode "B" Structural LR)
  right <- require (mkCellDoctrine mode "C" Computational LR)
  let morLeft = mkIdMorph "fLeft" base left
  let morRight = mkIdMorph "fRight" base right
  res <- case computePolyPushout "P" morLeft morRight of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  let cells = dCells2 (poDoctrine res)
  case findCell "eq" cells of
    Nothing -> assertFailure "expected merged cell"
    Just cell ->
      c2Class cell @?= Structural

testPushoutNameConflict :: Assertion
testPushoutNameConflict = do
  let mode = ModeName "M"
  base <- require (mkCellDoctrine mode "A" Computational LR)
  left <- require (mkCellDoctrine mode "B" Computational LR)
  right <- require (mkCellDoctrineWithAlt mode "C" Computational LR)
  let morLeft = mkIdMorph "fLeft" base left
  let morRight = mkIdMorph "fRight" base right
  case computePolyPushout "P" morLeft morRight of
    Left _ -> pure ()
    Right _ -> assertFailure "expected name conflict error"

mkCellDoctrine :: ModeName -> Text -> RuleClass -> Orientation -> Either Text Doctrine
mkCellDoctrine mode name cls orient = do
  let aName = TypeName "A"
  let gen = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdTyVars = []
        , gdIxVars = []
    , gdDom = map InPort [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        , gdAttrs = []
        }
  lhs <- genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName gen)
  let cell = Cell2
        { c2Name = "eq"
        , c2Class = cls
        , c2Orient = orient
        , c2TyVars = []
        , c2IxVars = []
        , c2LHS = lhs
        , c2RHS = lhs
        }
  let doc = Doctrine
        { dName = name
        , dModes = mkModes (S.singleton mode)
      , dIndexModes = S.empty
      , dIxTheory = M.empty
        , dTypes = M.fromList [(mode, M.fromList [(aName, TypeSig [])])]
        , dGens = M.fromList [(mode, M.fromList [(gdName gen, gen)])]
        , dCells2 = [cell]
        , dAttrSorts = M.empty
        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc

mkCellDoctrineWithAlt :: ModeName -> Text -> RuleClass -> Orientation -> Either Text Doctrine
mkCellDoctrineWithAlt mode name cls orient = do
  let aName = TypeName "A"
  let genF = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdTyVars = []
        , gdIxVars = []
    , gdDom = map InPort [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        , gdAttrs = []
        }
  let genG = GenDecl
        { gdName = GenName "g"
        , gdMode = mode
        , gdTyVars = []
        , gdIxVars = []
    , gdDom = map InPort [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        , gdAttrs = []
        }
  lhs <- genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName genG)
  let cell = Cell2
        { c2Name = "eq"
        , c2Class = cls
        , c2Orient = orient
        , c2TyVars = []
        , c2IxVars = []
        , c2LHS = lhs
        , c2RHS = lhs
        }
  let doc = Doctrine
        { dName = name
        , dModes = mkModes (S.singleton mode)
      , dIndexModes = S.empty
      , dIxTheory = M.empty
        , dTypes = M.fromList [(mode, M.fromList [(aName, TypeSig [])])]
        , dGens = M.fromList [(mode, M.fromList [(gdName genF, genF), (gdName genG, genG)])]
        , dCells2 = [cell]
        , dAttrSorts = M.empty
        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc

mkIdMorph :: Text -> Doctrine -> Doctrine -> Morphism
mkIdMorph name src tgt =
  let mode = ModeName "M"
      diag = case genD mode [tcon mode "A" []] [tcon mode "A" []] (GenName "f") of
        Left _ -> error "mkIdMorph: genD failed"
        Right d -> d
      genMap = M.fromList [((mode, GenName "f"), diag)]
  in Morphism
      { morName = name
      , morSrc = src
      , morTgt = tgt
      , morIsCoercion = False
      , morModeMap = identityModeMap src
      , morModMap = identityModMap src
      , morTypeMap = M.empty
      , morGenMap = genMap
      , morIxFunMap = M.empty
      , morAttrSortMap = M.empty
      , morPolicy = UseAllOriented
      , morFuel = 10
      }

findCell :: Text -> [Cell2] -> Maybe Cell2
findCell name = go
  where
    go [] = Nothing
    go (c:cs)
      | c2Name c == name = Just c
      | otherwise = go cs

testPushoutTypePermutationCommutes :: Assertion
testPushoutTypePermutationCommutes = do
  let mode = ModeName "M"
  let prod = TypeName "Prod"
  let pair = TypeName "Pair"
  let aVar = tvar mode "a"
  let bVar = tvar mode "b"
  base <- case mkTypeDoctrine mode "A" [(prod, 2)] of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  left <- case mkTypeDoctrine mode "B" [(pair, 2)] of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  right <- case mkTypeDoctrine mode "C" [(prod, 2)] of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  let tmplF = TypeTemplate [TPType aVar, TPType bVar] (TCon (TypeRef mode pair) [TAType (TVar bVar), TAType (TVar aVar)])
  let morF = Morphism
        { morName = "f"
        , morSrc = base
        , morTgt = left
        , morIsCoercion = False
        , morModeMap = identityModeMap base
        , morModMap = identityModMap base
        , morTypeMap = M.fromList [(TypeRef mode prod, tmplF)]
        , morGenMap = M.empty
      , morIxFunMap = M.empty
        , morAttrSortMap = M.empty
        , morPolicy = UseAllOriented
        , morFuel = 10
        }
  let morG = Morphism
        { morName = "g"
        , morSrc = base
        , morTgt = right
        , morIsCoercion = False
        , morModeMap = identityModeMap base
        , morModMap = identityModMap base
        , morTypeMap = M.empty
        , morGenMap = M.empty
      , morIxFunMap = M.empty
        , morAttrSortMap = M.empty
        , morPolicy = UseAllOriented
        , morFuel = 10
        }
  res <- case computePolyPushout "P" morF morG of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  let diagA = idD mode [TCon (TypeRef mode prod) [TAType (TVar aVar), TAType (TVar bVar)]]
  d1 <- case applyMorphismDiagram morF diagA of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  d2 <- case applyMorphismDiagram (poInl res) d1 of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  d3 <- case applyMorphismDiagram (poGlue res) diagA of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  iso <- case diagramIsoEq d2 d3 of
    Left err -> assertFailure (T.unpack err)
    Right ok -> pure ok
  assertBool "expected pushout type permutation to commute" iso

testPushoutRejectsModeMap :: Assertion
testPushoutRejectsModeMap = do
  let modeM = ModeName "M"
  let modeN = ModeName "N"
  let modes = mkModes (S.fromList [modeM, modeN])
  let base = Doctrine
        { dName = "Base"
        , dModes = modes
      , dIndexModes = S.empty
      , dIxTheory = M.empty
        , dTypes = M.empty
        , dGens = M.empty
        , dCells2 = []
        , dAttrSorts = M.empty
        }
  let left = base { dName = "Left" }
  let right = base { dName = "Right" }
  let modeMap = M.fromList [(modeM, modeN), (modeN, modeN)]
  let morF = Morphism
        { morName = "f"
        , morSrc = base
        , morTgt = left
        , morIsCoercion = False
        , morModeMap = modeMap
        , morModMap = identityModMap base
        , morTypeMap = M.empty
        , morGenMap = M.empty
      , morIxFunMap = M.empty
        , morAttrSortMap = M.empty
        , morPolicy = UseAllOriented
        , morFuel = 10
        }
  let morG = Morphism
        { morName = "g"
        , morSrc = base
        , morTgt = right
        , morIsCoercion = False
        , morModeMap = modeMap
        , morModMap = identityModMap base
        , morTypeMap = M.empty
        , morGenMap = M.empty
      , morIxFunMap = M.empty
        , morAttrSortMap = M.empty
        , morPolicy = UseAllOriented
        , morFuel = 10
        }
  case computePolyPushout "P" morF morG of
    Left err ->
      assertBool "expected mode map rejection" ("mode-preserving" `T.isInfixOf` err)
    Right _ -> assertFailure "expected pushout to reject non-identity mode map"

testPushoutAlphaRenameWithModeEq :: Assertion
testPushoutAlphaRenameWithModeEq = do
  let mode = ModeName "M"
  let modF = ModName "F"
  let modU = ModName "U"
  let mt = mkModeEqTheory mode modF modU
  base <- require (mkModeEqDoctrine "Base" mt "a" True)
  left <- require (mkModeEqDoctrine "Left" mt "x" False)
  right <- require (mkModeEqDoctrine "Right" mt "y" False)
  let morLeft = mkModeEqMorph "f" base left "x"
  let morRight = mkModeEqMorph "g" base right "y"
  res <- case computePolyPushout "P" morLeft morRight of
    Left err -> assertFailure (T.unpack err)
    Right out -> pure out
  case validateDoctrine (poDoctrine res) of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  let etaCells = [ cell | cell <- dCells2 (poDoctrine res), c2Name cell == "eta" ]
  length etaCells @?= 1
  case M.lookup mode (dGens (poDoctrine res)) >>= M.lookup (GenName "modal") of
    Nothing -> assertFailure "expected modal generator in pushout result"
    Just modalGen ->
      case gdPlainDom modalGen of
        [TMod me (TVar _)] -> mePath me @?= [modF]
        _ -> assertFailure "expected modal generator domain to retain non-canceling modality"

testPushoutIndexedTypeMaps :: Assertion
testPushoutIndexedTypeMaps = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let natRef = TypeRef modeI (TypeName "Nat")
  let vecRef = TypeRef modeM (TypeName "Vec")
  let vec2Ref = TypeRef modeM (TypeName "Vec2")
  let natTy = TCon natRef []
  let src =
        Doctrine
          { dName = "SrcIdx"
          , dModes = mkModes (S.fromList [modeM, modeI])
          , dIndexModes = S.singleton modeI
          , dIxTheory = M.empty
          , dTypes =
              M.fromList
                [ (modeI, M.fromList [(TypeName "Nat", TypeSig [])])
                , (modeM, M.fromList [(TypeName "Vec", TypeSig [PS_Ix natTy, PS_Ty modeM])])
                ]
          , dGens = M.empty
          , dCells2 = []
          , dAttrSorts = M.empty
          }
  let left =
        Doctrine
          { dName = "LeftIdx"
          , dModes = mkModes (S.fromList [modeM, modeI])
          , dIndexModes = S.singleton modeI
          , dIxTheory = M.empty
          , dTypes =
              M.fromList
                [ (modeI, M.fromList [(TypeName "Nat", TypeSig [])])
                , (modeM, M.fromList [(TypeName "Vec2", TypeSig [PS_Ix natTy, PS_Ty modeM])])
                ]
          , dGens = M.empty
          , dCells2 = []
          , dAttrSorts = M.empty
          }
  let right = src { dName = "RightIdx" }
  case validateDoctrine src of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine left of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine right of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  let nVar = IxVar { ixvName = "n", ixvSort = natTy, ixvScope = 0 }
  let aVar = TyVar { tvName = "a", tvMode = modeM }
  let morF =
        Morphism
          { morName = "fIdx"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap =
              M.fromList
                [ ( vecRef
                  , TypeTemplate
                      [TPIx nVar, TPType aVar]
                      (TCon vec2Ref [TAIndex (IXVar nVar), TAType (TVar aVar)])
                  )
                ]
          , morGenMap = M.empty
          , morIxFunMap = M.empty
          , morAttrSortMap = M.empty
          , morPolicy = UseAllOriented
          , morFuel = 10
          }
  let morG =
        Morphism
          { morName = "gIdx"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap = M.empty
          , morIxFunMap = M.empty
          , morAttrSortMap = M.empty
          , morPolicy = UseAllOriented
          , morFuel = 10
          }
  case computePolyPushout "PIdx" morF morG of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testPushoutCellIxAlphaEq :: Assertion
testPushoutCellIxAlphaEq = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let natTy = TCon (TypeRef modeI (TypeName "Nat")) []
  let vecRef = TypeRef modeM (TypeName "Vec")
  let genName = GenName "f"
  let mkIx name = IxVar { ixvName = name, ixvSort = natTy, ixvScope = 0 }
  let vecTy ixv = TCon vecRef [TAIndex (IXVar ixv)]
  let srcIx = mkIx "n"
  let leftIx = mkIx "i"
  let rightIx = mkIx "j"
  let srcGen =
        GenDecl
          { gdName = genName
          , gdMode = modeM
          , gdTyVars = []
          , gdIxVars = [srcIx]
          , gdDom = [InPort (vecTy srcIx)]
          , gdCod = [vecTy srcIx]
          , gdAttrs = []
          }
  let leftGen =
        GenDecl
          { gdName = genName
          , gdMode = modeM
          , gdTyVars = []
          , gdIxVars = [leftIx]
          , gdDom = [InPort (vecTy leftIx)]
          , gdCod = [vecTy leftIx]
          , gdAttrs = []
          }
  let rightGen =
        GenDecl
          { gdName = genName
          , gdMode = modeM
          , gdTyVars = []
          , gdIxVars = [rightIx]
          , gdDom = [InPort (vecTy rightIx)]
          , gdCod = [vecTy rightIx]
          , gdAttrs = []
          }
  leftLHS <- require (genD modeM [vecTy leftIx] [vecTy leftIx] genName)
  rightLHS <- require (genD modeM [vecTy rightIx] [vecTy rightIx] genName)
  let leftCell =
        Cell2
          { c2Name = "eqLeftIx"
          , c2Class = Computational
          , c2Orient = LR
          , c2TyVars = []
          , c2IxVars = [leftIx]
          , c2LHS = leftLHS
          , c2RHS = idD modeM [vecTy leftIx]
          }
  let rightCell =
        Cell2
          { c2Name = "eqRightIx"
          , c2Class = Computational
          , c2Orient = LR
          , c2TyVars = []
          , c2IxVars = [rightIx]
          , c2LHS = rightLHS
          , c2RHS = idD modeM [vecTy rightIx]
          }
  let commonDoc name gen cell =
        Doctrine
          { dName = name
          , dModes = mkModes (S.fromList [modeM, modeI])
          , dIndexModes = S.singleton modeI
          , dIxTheory = M.fromList [(modeI, IxTheory M.empty [])]
          , dTypes =
              M.fromList
                [ (modeI, M.fromList [(TypeName "Nat", TypeSig [])])
                , (modeM, M.fromList [(TypeName "Vec", TypeSig [PS_Ix natTy])])
                ]
          , dGens = M.fromList [(modeM, M.fromList [(genName, gen)])]
          , dCells2 = cell
          , dAttrSorts = M.empty
          }
  let src = commonDoc "SrcIxAlpha" srcGen []
  let left = commonDoc "LeftIxAlpha" leftGen [leftCell]
  let right = commonDoc "RightIxAlpha" rightGen [rightCell]
  case validateDoctrine src of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine left of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine right of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  img <- require (genD modeM [vecTy srcIx] [vecTy srcIx] genName)
  let morLeft =
        Morphism
          { morName = "fIxAlpha"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap = M.fromList [((modeM, genName), img)]
          , morIxFunMap = M.empty
          , morAttrSortMap = M.empty
          , morPolicy = UseAllOriented
          , morFuel = 10
          }
  let morRight =
        Morphism
          { morName = "gIxAlpha"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap = M.fromList [((modeM, genName), img)]
          , morIxFunMap = M.empty
          , morAttrSortMap = M.empty
          , morPolicy = UseAllOriented
          , morFuel = 10
          }
  res <- case computePolyPushout "PIxAlpha" morLeft morRight of
    Left err -> assertFailure (T.unpack err)
    Right out -> pure out
  length (dCells2 (poDoctrine res)) @?= 1

mkModeEqTheory :: ModeName -> ModName -> ModName -> ModeTheory
mkModeEqTheory mode modF modU =
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

mkModeEqMorph :: Text -> Doctrine -> Doctrine -> Text -> Morphism
mkModeEqMorph name src tgt varName =
  let mode = ModeName "M"
      modF = ModName "F"
      v = TyVar { tvName = varName, tvMode = mode }
      fExpr = ModExpr { meSrc = mode, meTgt = mode, mePath = [modF] }
      hTy = TVar v
      modalTy = TMod fExpr (TVar v)
      hImg = case genD mode [hTy] [hTy] (GenName "h") of
        Left _ -> error "mkModeEqMorph: genD h failed"
        Right d -> d
      modalImg = case genD mode [modalTy] [modalTy] (GenName "modal") of
        Left _ -> error "mkModeEqMorph: genD modal failed"
        Right d -> d
  in Morphism
      { morName = name
      , morSrc = src
      , morTgt = tgt
      , morIsCoercion = False
      , morModeMap = identityModeMap src
      , morModMap = identityModMap src
      , morTypeMap = M.empty
      , morGenMap = M.fromList [((mode, GenName "h"), hImg), ((mode, GenName "modal"), modalImg)]
      , morIxFunMap = M.empty
      , morAttrSortMap = M.empty
      , morPolicy = UseAllOriented
      , morFuel = 10
      }

mkModeEqDoctrine :: Text -> ModeTheory -> Text -> Bool -> Either Text Doctrine
mkModeEqDoctrine name mt varName useUF = do
  let mode = ModeName "M"
  let modF = ModName "F"
  let modU = ModName "U"
  let v = TyVar { tvName = varName, tvMode = mode }
  let fExpr = ModExpr { meSrc = mode, meTgt = mode, mePath = [modF] }
  let ufExpr = ModExpr { meSrc = mode, meTgt = mode, mePath = [modF, modU] }
  let hTy =
        if useUF
          then TMod ufExpr (TVar v)
          else TVar v
  let modalTy = TMod fExpr (TVar v)
  lhs <- genD mode [hTy] [hTy] (GenName "h")
  let cell = Cell2
        { c2Name = "eta"
        , c2Class = Computational
        , c2Orient = LR
        , c2TyVars = [v]
        , c2IxVars = []
        , c2LHS = lhs
        , c2RHS = idD mode [hTy]
        }
  let genH = GenDecl
        { gdName = GenName "h"
        , gdMode = mode
        , gdTyVars = [v]
        , gdIxVars = []
    , gdDom = map InPort [TVar v]
        , gdCod = [TVar v]
        , gdAttrs = []
        }
  let genModal = GenDecl
        { gdName = GenName "modal"
        , gdMode = mode
        , gdTyVars = [v]
        , gdIxVars = []
    , gdDom = map InPort [modalTy]
        , gdCod = [modalTy]
        , gdAttrs = []
        }
  let doc = Doctrine
        { dName = name
        , dModes = mt
      , dIndexModes = S.empty
      , dIxTheory = M.empty
        , dTypes = M.empty
        , dGens = M.fromList [(mode, M.fromList [(GenName "h", genH), (GenName "modal", genModal)])]
        , dCells2 = [cell]
        , dAttrSorts = M.empty
        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc

mkTypeDoctrine :: ModeName -> Text -> [(TypeName, Int)] -> Either Text Doctrine
mkTypeDoctrine mode name types = do
  let types' = M.fromList [ (tname, TypeSig (replicate arity (PS_Ty mode))) | (tname, arity) <- types ]
  let doc = Doctrine
        { dName = name
        , dModes = mkModes (S.singleton mode)
      , dIndexModes = S.empty
      , dIxTheory = M.empty
        , dTypes = M.fromList [(mode, types')]
        , dGens = M.empty
        , dCells2 = []
        , dAttrSorts = M.empty
        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc
