{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Morphism
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Common.Rules (RewritePolicy(..), RuleClass(..), Orientation(..))
import Strat.Poly.ModeTheory
import Strat.Poly.TypeExpr
import Strat.Poly.Names
import Strat.Poly.Diagram
import Strat.Poly.Cell2
import Strat.Poly.Doctrine
import Strat.Poly.Morphism


tests :: TestTree
tests =
  testGroup
    "Poly.Morphism"
    [ testCase "monoid morphism to string monoid" testMonoidMorphism
    , testCase "type map can reorder parameters" testTypeMapReorder
    , testCase "cross-mode morphism applies mode map" testCrossModeMorphism
    ]

tvar :: ModeName -> Text -> TyVar
tvar mode name = TyVar { tvName = name, tvMode = mode }

tcon :: ModeName -> Text -> [TypeExpr] -> TypeExpr
tcon mode name args = TCon (TypeRef mode (TypeName name)) args

identityModeMap :: Doctrine -> M.Map ModeName ModeName
identityModeMap doc =
  M.fromList [ (m, m) | m <- S.toList (mtModes (dModes doc)) ]

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
  let genSrc = GenDecl genName mode [a, b] [TCon (TypeRef mode prod) [TVar a, TVar b]] [TCon (TypeRef mode prod) [TVar a, TVar b]]
  let genTgt = GenDecl genName mode [a, b] [TCon (TypeRef mode pair) [TVar a, TVar b]] [TCon (TypeRef mode pair) [TVar a, TVar b]]
  let docSrc = Doctrine
        { dName = "Src"
        , dModes = ModeTheory (S.singleton mode) M.empty []
        , dTypes = M.fromList [(mode, M.fromList [(prod, TypeSig [mode, mode])])]
        , dGens = M.fromList [(mode, M.fromList [(genName, genSrc)])]
        , dCells2 = []
        }
  let docTgt = Doctrine
        { dName = "Tgt"
        , dModes = ModeTheory (S.singleton mode) M.empty []
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
  let fGen = GenDecl (GenName "f") modeC [] [aTy] [aTy]
  let gGen = GenDecl (GenName "g") modeV [] [bTy] [bTy]
  let docSrc = Doctrine
        { dName = "Src"
        , dModes = ModeTheory (S.singleton modeC) M.empty []
        , dTypes = M.fromList [(modeC, M.fromList [(TypeName "A", TypeSig [])])]
        , dGens = M.fromList [(modeC, M.fromList [(GenName "f", fGen)])]
        , dCells2 = []
        }
  let docTgt = Doctrine
        { dName = "Tgt"
        , dModes = ModeTheory (S.singleton modeV) M.empty []
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

modeM :: ModeName
modeM = ModeName "M"

aTy :: TypeExpr
aTy = TCon (TypeRef modeM (TypeName "A")) []

strTy :: TypeExpr
strTy = TCon (TypeRef modeM (TypeName "Str")) []

mkMonoid :: Either Text Doctrine
mkMonoid = do
  let mt = ModeTheory (S.singleton modeM) M.empty []
  let types = M.fromList [(modeM, M.fromList [(TypeName "A", TypeSig [])])]
  assoc <- assocRule "assoc" aTy (GenName "mul")
  unitL <- unitRule "unitL" aTy (GenName "unit") (GenName "mul") True
  unitR <- unitRule "unitR" aTy (GenName "unit") (GenName "mul") False
  let gens = M.fromList [(modeM, M.fromList [(GenName "unit", GenDecl (GenName "unit") modeM [] [] [aTy]), (GenName "mul", GenDecl (GenName "mul") modeM [] [aTy, aTy] [aTy])])]
  let doc = Doctrine
        { dName = "Monoid"
        , dModes = mt
        , dTypes = types
        , dGens = gens
        , dCells2 = [assoc, unitL, unitR]
        }
  case validateDoctrine doc of
    Left err -> Left err
    Right () -> Right doc

mkStringMonoid :: Either Text Doctrine
mkStringMonoid = do
  let mt = ModeTheory (S.singleton modeM) M.empty []
  let types = M.fromList [(modeM, M.fromList [(TypeName "Str", TypeSig [])])]
  assoc <- assocRule "assoc" strTy (GenName "append")
  unitL <- unitRule "unitL" strTy (GenName "empty") (GenName "append") True
  unitR <- unitRule "unitR" strTy (GenName "empty") (GenName "append") False
  let gens = M.fromList [(modeM, M.fromList [(GenName "empty", GenDecl (GenName "empty") modeM [] [] [strTy]), (GenName "append", GenDecl (GenName "append") modeM [] [strTy, strTy] [strTy])])]
  let doc = Doctrine
        { dName = "StringMonoid"
        , dModes = mt
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
  lhs <- compD mul left
  right <- tensorD id1 mul
  rhs <- compD mul right
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
        compD mul tens
      else do
        tens <- tensorD id1 unit
        compD mul tens
  pure Cell2
    { c2Name = name
    , c2Class = Computational
    , c2Orient = LR
    , c2TyVars = []
    , c2LHS = expr
    , c2RHS = id1
    }
