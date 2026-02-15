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
import qualified Data.IntMap.Strict as IM
import Strat.Poly.ModeTheory (ModeName(..), ModName(..), ModExpr(..), ModDecl(..), ModEqn(..), ModeTheory(..), ModeInfo(..), mtModes, mtDecls)
import Strat.Poly.TypeExpr (TyVar(..), TypeName(..), TypeRef(..), TypeExpr(..), TypeArg(..), TmVar(..), TermDiagram(..), typeMode)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram (genD, idD)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..), ParamSig(..), InputShape(..), BinderSig(..), gdPlainDom, validateDoctrine)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Morphism (Morphism(..), MorphismCheck(..), GenImage(..), TemplateParam(..), TypeTemplate(..), applyMorphismDiagram)
import Strat.Poly.Pushout (computePolyPushout, PolyPushoutResult(..))
import Strat.Poly.Graph (diagramIsoEq, Diagram(..), BinderArg(..), BinderMetaVar(..), Edge(..), EdgePayload(..), emptyDiagram, freshPort, addEdgePayload)
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
    , testCase "pushout supports term-parameterized type maps" testPushoutTermTypeMaps
    , testCase "pushout merges cells alpha-equivalent over term vars" testPushoutCellTmAlphaEq
    , testCase "pushout injection morphism preserves concrete binder arguments" testPushoutInjectionPreservesBinderArgs
    , testCase "pushout accepts renaming morphisms with binder signatures in target doctrine" testPushoutAcceptsRenamingWithBinders
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

plainImage :: Diagram -> GenImage
plainImage diag = GenImage diag M.empty

setSingleEdgeBargs :: Diagram -> [BinderArg] -> Either Text Diagram
setSingleEdgeBargs diag bargs =
  case IM.toList (dEdges diag) of
    [(edgeKey, edge@(Edge _ (PGen g attrs _) _ _))] ->
      let edge' = edge { ePayload = PGen g attrs bargs }
      in pure diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
    _ -> Left "expected a single generator edge"

tvar :: ModeName -> Text -> TyVar
tvar mode name = TyVar { tvName = name, tvMode = mode }

tcon :: ModeName -> Text -> [TypeExpr] -> TypeExpr
tcon mode name args = TCon (TypeRef mode (TypeName name)) (map TAType args)

tmMeta :: TmVar -> TermDiagram
tmMeta v =
  let mode = typeMode (tmvSort v)
      (outPid, d0) = freshPort (tmvSort v) (emptyDiagram mode [])
      d1 =
        case addEdgePayload (PTmMeta v) [] [outPid] d0 of
          Left err -> error (T.unpack err)
          Right d -> d
  in TermDiagram d1 { dOut = [outPid] }

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
    { mtModes = M.fromList [ (m, ModeInfo m) | m <- S.toList modes ]
    , mtDecls = M.empty
    , mtEqns = []
    }


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
        , gdTmVars = []
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
        , c2TmVars = []
        , c2LHS = lhs
        , c2RHS = rhs
        }
  let doc = Doctrine
        { dName = name
        , dModes = mkModes (S.singleton mode)
    , dAcyclicModes = S.empty
        , dTypes = M.empty
        , dGens = M.fromList [(mode, M.fromList [(gdName gen, gen)])]
        , dCells2 = [cell]
      , dActions = M.empty
      , dObligations = []
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
      genMap = M.fromList [((mode, GenName "f"), plainImage diag)]
  in Morphism
      { morName = name
      , morSrc = src
      , morTgt = tgt
      , morIsCoercion = False
      , morModeMap = identityModeMap src
      , morModMap = identityModMap src
      , morTypeMap = M.empty
      , morGenMap = genMap
        , morCheck = CheckAll
      , morAttrSortMap = M.empty
      , morPolicy = UseAllOriented
      }

testPushoutMergeOrient :: Assertion
testPushoutMergeOrient = do
  let mode = ModeName "M"
  base <- require (mkCellDoctrine mode "A" Structural LR)
  left <- require (mkCellDoctrine mode "B" Structural LR)
  right <- require (mkCellDoctrine mode "C" Structural RL)
  let morLeft = mkIdMorph "fLeft" base left
  let morRight = mkIdMorph "fRight" base right
  case computePolyPushout "P" morLeft morRight of
    Left err ->
      assertBool
        ("expected morphism-check rejection, got: " <> T.unpack err)
        ("equation violation" `T.isInfixOf` err || "equation undecided" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected pushout to reject non-preserving glue morphism"

testPushoutMergeClass :: Assertion
testPushoutMergeClass = do
  let mode = ModeName "M"
  base <- require (mkCellDoctrine mode "A" Computational LR)
  left <- require (mkCellDoctrine mode "B" Structural LR)
  right <- require (mkCellDoctrine mode "C" Computational LR)
  let morLeft = mkIdMorph "fLeft" base left
  let morRight = mkIdMorph "fRight" base right
  case computePolyPushout "P" morLeft morRight of
    Left err ->
      assertBool
        ("expected morphism-check rejection, got: " <> T.unpack err)
        ("equation violation" `T.isInfixOf` err || "equation undecided" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected pushout to reject non-preserving glue morphism"

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
  let genF = GenDecl
        { gdName = GenName "f"
        , gdMode = mode
        , gdTyVars = []
        , gdTmVars = []
        , gdDom = map InPort [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        , gdAttrs = []
        }
  let genG = GenDecl
        { gdName = GenName "g"
        , gdMode = mode
        , gdTyVars = []
        , gdTmVars = []
        , gdDom = map InPort [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        , gdAttrs = []
        }
  lhs <- genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName genF)
  rhs <- genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName genG)
  let cell = Cell2
        { c2Name = "eq"
        , c2Class = cls
        , c2Orient = orient
        , c2TyVars = []
        , c2TmVars = []
        , c2LHS = lhs
        , c2RHS = rhs
        }
  let doc = Doctrine
        { dName = name
        , dModes = mkModes (S.singleton mode)
        , dAcyclicModes = S.empty
        , dTypes = M.fromList [(mode, M.fromList [(aName, TypeSig [])])]
        , dGens = M.fromList [(mode, M.fromList [(gdName genF, genF), (gdName genG, genG)])]
        , dCells2 = [cell]
        , dActions = M.empty
        , dObligations = []
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
        , gdTmVars = []
    , gdDom = map InPort [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        , gdAttrs = []
        }
  let genG = GenDecl
        { gdName = GenName "g"
        , gdMode = mode
        , gdTyVars = []
        , gdTmVars = []
        , gdDom = map InPort [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        , gdAttrs = []
        }
  lhs <- genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName genG)
  rhs <- genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName genF)
  let cell = Cell2
        { c2Name = "eq"
        , c2Class = cls
        , c2Orient = orient
        , c2TyVars = []
        , c2TmVars = []
        , c2LHS = lhs
        , c2RHS = rhs
        }
  let doc = Doctrine
        { dName = name
        , dModes = mkModes (S.singleton mode)
        , dAcyclicModes = S.empty
        , dTypes = M.fromList [(mode, M.fromList [(aName, TypeSig [])])]
        , dGens = M.fromList [(mode, M.fromList [(gdName genF, genF), (gdName genG, genG)])]
        , dCells2 = [cell]
        , dActions = M.empty
        , dObligations = []
        , dAttrSorts = M.empty
        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc

mkIdMorph :: Text -> Doctrine -> Doctrine -> Morphism
mkIdMorph name src tgt =
  let mode = ModeName "M"
      mkImage gName =
        case genD mode [tcon mode "A" []] [tcon mode "A" []] gName of
          Left _ -> error "mkIdMorph: genD failed"
          Right d -> plainImage d
      genMap =
        M.fromList
          [ ((mode, GenName "f"), mkImage (GenName "f"))
          , ((mode, GenName "g"), mkImage (GenName "g"))
          ]
  in Morphism
      { morName = name
      , morSrc = src
      , morTgt = tgt
      , morIsCoercion = False
      , morModeMap = identityModeMap src
      , morModMap = identityModMap src
      , morTypeMap = M.empty
      , morGenMap = genMap
        , morCheck = CheckAll
      , morAttrSortMap = M.empty
      , morPolicy = UseAllOriented
      }

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
        , morCheck = CheckAll
        , morAttrSortMap = M.empty
        , morPolicy = UseAllOriented
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
        , morCheck = CheckAll
        , morAttrSortMap = M.empty
        , morPolicy = UseAllOriented
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
    , dAcyclicModes = S.empty
        , dTypes = M.empty
        , dGens = M.empty
        , dCells2 = []
      , dActions = M.empty
      , dObligations = []
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
        , morCheck = CheckAll
        , morAttrSortMap = M.empty
        , morPolicy = UseAllOriented
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
        , morCheck = CheckAll
        , morAttrSortMap = M.empty
        , morPolicy = UseAllOriented
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

testPushoutTermTypeMaps :: Assertion
testPushoutTermTypeMaps = do
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
    , dAcyclicModes = S.empty
          , dTypes =
              M.fromList
                [ (modeI, M.fromList [(TypeName "Nat", TypeSig [])])
                , (modeM, M.fromList [(TypeName "Vec", TypeSig [PS_Tm natTy, PS_Ty modeM])])
                ]
          , dGens = M.empty
          , dCells2 = []
      , dActions = M.empty
      , dObligations = []
          , dAttrSorts = M.empty
          }
  let left =
        Doctrine
          { dName = "LeftIdx"
          , dModes = mkModes (S.fromList [modeM, modeI])
    , dAcyclicModes = S.empty
          , dTypes =
              M.fromList
                [ (modeI, M.fromList [(TypeName "Nat", TypeSig [])])
                , (modeM, M.fromList [(TypeName "Vec2", TypeSig [PS_Tm natTy, PS_Ty modeM])])
                ]
          , dGens = M.empty
          , dCells2 = []
      , dActions = M.empty
      , dObligations = []
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
  let nVar = TmVar { tmvName = "n", tmvSort = natTy, tmvScope = 0 }
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
                      [TPTm nVar, TPType aVar]
                      (TCon vec2Ref [TATm (tmMeta nVar), TAType (TVar aVar)])
                  )
                ]
          , morGenMap = M.empty
        , morCheck = CheckAll
          , morAttrSortMap = M.empty
          , morPolicy = UseAllOriented
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
        , morCheck = CheckAll
          , morAttrSortMap = M.empty
          , morPolicy = UseAllOriented
          }
  case computePolyPushout "PIdx" morF morG of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testPushoutCellTmAlphaEq :: Assertion
testPushoutCellTmAlphaEq = do
  let modeM = ModeName "M"
  let modeI = ModeName "I"
  let natTy = TCon (TypeRef modeI (TypeName "Nat")) []
  let vecRef = TypeRef modeM (TypeName "Vec")
  let genName = GenName "f"
  let mkTm name = TmVar { tmvName = name, tmvSort = natTy, tmvScope = 0 }
  let vecTy tmVar = TCon vecRef [TATm (tmMeta tmVar)]
  let srcTm = mkTm "n"
  let leftTm = mkTm "i"
  let rightTm = mkTm "j"
  let zDecl =
        GenDecl
          { gdName = GenName "Z"
          , gdMode = modeI
          , gdTyVars = []
          , gdTmVars = []
          , gdDom = []
          , gdCod = [natTy]
          , gdAttrs = []
          }
  let srcGen =
        GenDecl
          { gdName = genName
          , gdMode = modeM
          , gdTyVars = []
          , gdTmVars = [srcTm]
          , gdDom = [InPort (vecTy srcTm)]
          , gdCod = [vecTy srcTm]
          , gdAttrs = []
          }
  let leftGen =
        GenDecl
          { gdName = genName
          , gdMode = modeM
          , gdTyVars = []
          , gdTmVars = [leftTm]
          , gdDom = [InPort (vecTy leftTm)]
          , gdCod = [vecTy leftTm]
          , gdAttrs = []
          }
  let rightGen =
        GenDecl
          { gdName = genName
          , gdMode = modeM
          , gdTyVars = []
          , gdTmVars = [rightTm]
          , gdDom = [InPort (vecTy rightTm)]
          , gdCod = [vecTy rightTm]
          , gdAttrs = []
          }
  leftLHS <- require (genD modeM [vecTy leftTm] [vecTy leftTm] genName)
  rightLHS <- require (genD modeM [vecTy rightTm] [vecTy rightTm] genName)
  let leftCell =
        Cell2
          { c2Name = "eqLeftTm"
          , c2Class = Computational
          , c2Orient = LR
          , c2TyVars = []
          , c2TmVars = [leftTm]
          , c2LHS = leftLHS
          , c2RHS = idD modeM [vecTy leftTm]
          }
  let rightCell =
        Cell2
          { c2Name = "eqRightTm"
          , c2Class = Computational
          , c2Orient = LR
          , c2TyVars = []
          , c2TmVars = [rightTm]
          , c2LHS = rightLHS
          , c2RHS = idD modeM [vecTy rightTm]
          }
  let commonDoc name gen cell =
        Doctrine
          { dName = name
          , dModes = mkModes (S.fromList [modeM, modeI])
    , dAcyclicModes = S.empty
          , dTypes =
              M.fromList
                [ (modeI, M.fromList [(TypeName "Nat", TypeSig [])])
                , (modeM, M.fromList [(TypeName "Vec", TypeSig [PS_Tm natTy])])
                ]
          , dGens =
              M.fromList
                [ (modeI, M.fromList [(GenName "Z", zDecl)])
                , (modeM, M.fromList [(genName, gen)])
                ]
          , dCells2 = cell
        , dActions = M.empty
        , dObligations = []
          , dAttrSorts = M.empty
          }
  let src = commonDoc "SrcTmAlpha" srcGen []
  let left = commonDoc "LeftTmAlpha" leftGen [leftCell]
  let right = commonDoc "RightTmAlpha" rightGen [rightCell]
  case validateDoctrine src of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine left of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine right of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  img <- require (genD modeM [vecTy srcTm] [vecTy srcTm] genName)
  zImg <- require (genD modeI [] [natTy] (GenName "Z"))
  let morLeft =
        Morphism
          { morName = "fTmAlpha"
          , morSrc = src
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                [ ((modeI, GenName "Z"), plainImage zImg)
                , ((modeM, genName), plainImage img)
                ]
        , morCheck = CheckAll
          , morAttrSortMap = M.empty
          , morPolicy = UseAllOriented
          }
  let morRight =
        Morphism
          { morName = "gTmAlpha"
          , morSrc = src
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap src
          , morModMap = identityModMap src
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                [ ((modeI, GenName "Z"), plainImage zImg)
                , ((modeM, genName), plainImage img)
                ]
        , morCheck = CheckAll
          , morAttrSortMap = M.empty
          , morPolicy = UseAllOriented
          }
  res <- case computePolyPushout "PTmAlpha" morLeft morRight of
    Left err -> assertFailure (T.unpack err)
    Right out -> pure out
  length (dCells2 (poDoctrine res)) @?= 1

testPushoutInjectionPreservesBinderArgs :: Assertion
testPushoutInjectionPreservesBinderArgs = do
  let mode = ModeName "M"
  let aTy = TCon (TypeRef mode (TypeName "A")) []
  let gName = GenName "g"
  let slotSig = BinderSig { bsTmCtx = [], bsDom = [aTy], bsCod = [aTy] }
  let gDecl =
        GenDecl
          { gdName = gName
          , gdMode = mode
          , gdTyVars = []
          , gdTmVars = []
          , gdDom = [InBinder slotSig]
          , gdCod = [aTy]
          , gdAttrs = []
          }
  let iface =
        Doctrine
          { dName = "IfaceBinder"
          , dModes = mkModes (S.singleton mode)
    , dAcyclicModes = S.empty
          , dTypes = M.empty
          , dGens = M.empty
          , dCells2 = []
      , dActions = M.empty
      , dObligations = []
          , dAttrSorts = M.empty
          }
  let left =
        iface
          { dName = "LeftBinder"
          , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])]
          , dGens = M.fromList [(mode, M.fromList [(gName, gDecl)])]
          }
  let right = iface { dName = "RightBinder" }
  case validateDoctrine iface of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine left of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine right of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  let mkIfaceIn name tgt =
        Morphism
          { morName = name
          , morSrc = iface
          , morTgt = tgt
          , morIsCoercion = False
          , morModeMap = identityModeMap iface
          , morModMap = identityModMap iface
          , morTypeMap = M.empty
          , morGenMap = M.empty
        , morCheck = CheckAll
          , morAttrSortMap = M.empty
          , morPolicy = UseAllOriented
          }
  let morLeft = mkIfaceIn "iface.left" left
  let morRight = mkIfaceIn "iface.right" right
  res <- case computePolyPushout "PBindInj" morLeft morRight of
    Left err -> assertFailure (T.unpack err)
    Right out -> pure out
  let body = idD mode [aTy]
  leftDiag0 <- require (genD mode [] [aTy] gName)
  leftDiag <- require (setSingleEdgeBargs leftDiag0 [BAConcrete body])
  mapped <- case applyMorphismDiagram (poInl res) leftDiag of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  case IM.elems (dEdges mapped) of
    [Edge _ (PGen _ _ [BAConcrete _]) _ _] -> pure ()
    _ -> assertFailure "expected mapped injection image to preserve one concrete binder argument"

testPushoutAcceptsRenamingWithBinders :: Assertion
testPushoutAcceptsRenamingWithBinders = do
  let mode = ModeName "M"
  let aRef = TypeRef mode (TypeName "A")
  let a1Ref = TypeRef mode (TypeName "A1")
  let aTy = TCon aRef []
  let a1Ty = TCon a1Ref []
  let gName = GenName "g"
  let g1Name = GenName "g1"
  let slotSigSrc = BinderSig { bsTmCtx = [], bsDom = [aTy], bsCod = [aTy] }
  let slotSigTgt = BinderSig { bsTmCtx = [], bsDom = [a1Ty], bsCod = [a1Ty] }
  let ifaceGen =
        GenDecl
          { gdName = gName
          , gdMode = mode
          , gdTyVars = []
          , gdTmVars = []
          , gdDom = [InBinder slotSigSrc]
          , gdCod = [aTy]
          , gdAttrs = []
          }
  let leftGen =
        GenDecl
          { gdName = g1Name
          , gdMode = mode
          , gdTyVars = []
          , gdTmVars = []
          , gdDom = [InBinder slotSigTgt]
          , gdCod = [a1Ty]
          , gdAttrs = []
          }
  let iface =
        Doctrine
          { dName = "IfaceRenameBinder"
          , dModes = mkModes (S.singleton mode)
    , dAcyclicModes = S.empty
          , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])]
          , dGens = M.fromList [(mode, M.fromList [(gName, ifaceGen)])]
          , dCells2 = []
      , dActions = M.empty
      , dObligations = []
          , dAttrSorts = M.empty
          }
  let left =
        Doctrine
          { dName = "LeftRenameBinder"
          , dModes = mkModes (S.singleton mode)
    , dAcyclicModes = S.empty
          , dTypes = M.fromList [(mode, M.fromList [(TypeName "A1", TypeSig [])])]
          , dGens = M.fromList [(mode, M.fromList [(g1Name, leftGen)])]
          , dCells2 = []
      , dActions = M.empty
      , dObligations = []
          , dAttrSorts = M.empty
          }
  let right = iface { dName = "RightRenameBinder" }
  case validateDoctrine iface of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine left of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  case validateDoctrine right of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  let hole = BinderMetaVar "b0"
  imgLeft0 <- require (genD mode [] [a1Ty] g1Name)
  imgLeft <- require (setSingleEdgeBargs imgLeft0 [BAMeta hole])
  imgRight0 <- require (genD mode [] [aTy] gName)
  imgRight <- require (setSingleEdgeBargs imgRight0 [BAMeta hole])
  let morLeft =
        Morphism
          { morName = "fRenameBinder"
          , morSrc = iface
          , morTgt = left
          , morIsCoercion = False
          , morModeMap = identityModeMap iface
          , morModMap = identityModMap iface
          , morTypeMap = M.fromList [(aRef, TypeTemplate [] a1Ty)]
          , morGenMap = M.fromList [((mode, gName), GenImage imgLeft (M.fromList [(hole, slotSigTgt)]))]
        , morCheck = CheckAll
          , morAttrSortMap = M.empty
          , morPolicy = UseAllOriented
          }
  let morRight =
        Morphism
          { morName = "gRenameBinder"
          , morSrc = iface
          , morTgt = right
          , morIsCoercion = False
          , morModeMap = identityModeMap iface
          , morModMap = identityModMap iface
          , morTypeMap = M.empty
          , morGenMap = M.fromList [((mode, gName), GenImage imgRight (M.fromList [(hole, slotSigSrc)]))]
        , morCheck = CheckAll
          , morAttrSortMap = M.empty
          , morPolicy = UseAllOriented
          }
  case computePolyPushout "PRenameBinder" morLeft morRight of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

mkModeEqTheory :: ModeName -> ModName -> ModName -> ModeTheory
mkModeEqTheory mode modF modU =
  ModeTheory
    { mtModes = M.singleton mode (ModeInfo mode)
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
      , morGenMap = M.fromList [((mode, GenName "h"), plainImage hImg), ((mode, GenName "modal"), plainImage modalImg)]
        , morCheck = CheckAll
      , morAttrSortMap = M.empty
      , morPolicy = UseAllOriented
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
        , c2TmVars = []
        , c2LHS = lhs
        , c2RHS = idD mode [hTy]
        }
  let genH = GenDecl
        { gdName = GenName "h"
        , gdMode = mode
        , gdTyVars = [v]
        , gdTmVars = []
    , gdDom = map InPort [TVar v]
        , gdCod = [TVar v]
        , gdAttrs = []
        }
  let genModal = GenDecl
        { gdName = GenName "modal"
        , gdMode = mode
        , gdTyVars = [v]
        , gdTmVars = []
    , gdDom = map InPort [modalTy]
        , gdCod = [modalTy]
        , gdAttrs = []
        }
  let doc = Doctrine
        { dName = name
        , dModes = mt
    , dAcyclicModes = S.empty
        , dTypes = M.empty
        , dGens = M.fromList [(mode, M.fromList [(GenName "h", genH), (GenName "modal", genModal)])]
        , dCells2 = [cell]
      , dActions = M.empty
      , dObligations = []
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
    , dAcyclicModes = S.empty
        , dTypes = M.fromList [(mode, types')]
        , dGens = M.empty
        , dCells2 = []
      , dActions = M.empty
      , dObligations = []
        , dAttrSorts = M.empty
        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc
