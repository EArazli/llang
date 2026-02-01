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
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.TypeExpr (TyVar(..), TypeName(..), TypeRef(..), TypeExpr(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Diagram (genD, idD)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..), validateDoctrine)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Morphism (Morphism(..), TypeTemplate(..), applyMorphismDiagram)
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
    ]

require :: Either Text a -> IO a
require = either (assertFailure . T.unpack) pure

tvar :: ModeName -> Text -> TyVar
tvar mode name = TyVar { tvName = name, tvMode = mode }

tcon :: ModeName -> Text -> [TypeExpr] -> TypeExpr
tcon mode name args = TCon (TypeRef mode (TypeName name)) args

identityModeMap :: Doctrine -> M.Map ModeName ModeName
identityModeMap doc =
  M.fromList [ (m, m) | m <- S.toList (mtModes (dModes doc)) ]


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
        , gdDom = [TVar tyVar]
        , gdCod = [TVar tyVar]
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
        , c2LHS = lhs
        , c2RHS = rhs
        }
  let doc = Doctrine
        { dName = name
        , dModes = ModeTheory (S.singleton mode) M.empty []
        , dTypes = M.empty
        , dGens = M.fromList [(mode, M.fromList [(gdName gen, gen)])]
        , dCells2 = [cell]
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
      , morTypeMap = M.empty
      , morGenMap = genMap
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
        , gdDom = [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        }
  lhs <- genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName gen)
  let cell = Cell2
        { c2Name = "eq"
        , c2Class = cls
        , c2Orient = orient
        , c2TyVars = []
        , c2LHS = lhs
        , c2RHS = lhs
        }
  let doc = Doctrine
        { dName = name
        , dModes = ModeTheory (S.singleton mode) M.empty []
        , dTypes = M.fromList [(mode, M.fromList [(aName, TypeSig [])])]
        , dGens = M.fromList [(mode, M.fromList [(gdName gen, gen)])]
        , dCells2 = [cell]
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
        , gdDom = [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        }
  let genG = GenDecl
        { gdName = GenName "g"
        , gdMode = mode
        , gdTyVars = []
        , gdDom = [tcon mode "A" []]
        , gdCod = [tcon mode "A" []]
        }
  lhs <- genD mode [tcon mode "A" []] [tcon mode "A" []] (gdName genG)
  let cell = Cell2
        { c2Name = "eq"
        , c2Class = cls
        , c2Orient = orient
        , c2TyVars = []
        , c2LHS = lhs
        , c2RHS = lhs
        }
  let doc = Doctrine
        { dName = name
        , dModes = ModeTheory (S.singleton mode) M.empty []
        , dTypes = M.fromList [(mode, M.fromList [(aName, TypeSig [])])]
        , dGens = M.fromList [(mode, M.fromList [(gdName genF, genF), (gdName genG, genG)])]
        , dCells2 = [cell]
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
      , morTypeMap = M.empty
      , morGenMap = genMap
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
  let tmplF = TypeTemplate [aVar, bVar] (TCon (TypeRef mode pair) [TVar bVar, TVar aVar])
  let morF = Morphism
        { morName = "f"
        , morSrc = base
        , morTgt = left
        , morIsCoercion = False
        , morModeMap = identityModeMap base
        , morTypeMap = M.fromList [(TypeRef mode prod, tmplF)]
        , morGenMap = M.empty
        , morPolicy = UseAllOriented
        , morFuel = 10
        }
  let morG = Morphism
        { morName = "g"
        , morSrc = base
        , morTgt = right
        , morIsCoercion = False
        , morModeMap = identityModeMap base
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morPolicy = UseAllOriented
        , morFuel = 10
        }
  res <- case computePolyPushout "P" morF morG of
    Left err -> assertFailure (T.unpack err)
    Right r -> pure r
  let diagA = idD mode [TCon (TypeRef mode prod) [TVar aVar, TVar bVar]]
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
  let modes = ModeTheory (S.fromList [modeM, modeN]) M.empty []
  let base = Doctrine
        { dName = "Base"
        , dModes = modes
        , dTypes = M.empty
        , dGens = M.empty
        , dCells2 = []
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
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morPolicy = UseAllOriented
        , morFuel = 10
        }
  let morG = Morphism
        { morName = "g"
        , morSrc = base
        , morTgt = right
        , morIsCoercion = False
        , morModeMap = modeMap
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morPolicy = UseAllOriented
        , morFuel = 10
        }
  case computePolyPushout "P" morF morG of
    Left err ->
      assertBool "expected mode map rejection" ("mode-preserving" `T.isInfixOf` err)
    Right _ -> assertFailure "expected pushout to reject non-identity mode map"

mkTypeDoctrine :: ModeName -> Text -> [(TypeName, Int)] -> Either Text Doctrine
mkTypeDoctrine mode name types = do
  let types' = M.fromList [ (tname, TypeSig (replicate arity mode)) | (tname, arity) <- types ]
  let doc = Doctrine
        { dName = name
        , dModes = ModeTheory (S.singleton mode) M.empty []
        , dTypes = M.fromList [(mode, types')]
        , dGens = M.empty
        , dCells2 = []
        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc
