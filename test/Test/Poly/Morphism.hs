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
import Strat.Kernel.RewriteSystem (RewritePolicy(..))
import Strat.Kernel.Types (RuleClass(..), Orientation(..))
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
    ]

testMonoidMorphism :: Assertion
testMonoidMorphism = do
  docSrc <- either (assertFailure . T.unpack) pure mkMonoid
  docTgt <- either (assertFailure . T.unpack) pure mkStringMonoid
  let typeMap = M.fromList [((modeM, TypeName "A"), TCon (TypeName "Str") [])]
  unitImg <- either (assertFailure . T.unpack) pure (genD modeM [] [TCon (TypeName "Str") []] (GenName "empty"))
  mulImg <- either (assertFailure . T.unpack) pure (genD modeM [TCon (TypeName "Str") [], TCon (TypeName "Str") []] [TCon (TypeName "Str") []] (GenName "append"))
  let mor = Morphism
        { morName = "MonoidToStr"
        , morSrc = docSrc
        , morTgt = docTgt
        , morTypeMap = typeMap
        , morGenMap = M.fromList [((modeM, GenName "unit"), unitImg), ((modeM, GenName "mul"), mulImg)]
        , morPolicy = UseAllOriented
        , morFuel = 20
        }
  case checkMorphism mor of
    Left err -> assertFailure (show err)
    Right () -> pure ()

modeM :: ModeName
modeM = ModeName "M"

aTy :: TypeExpr
aTy = TCon (TypeName "A") []

strTy :: TypeExpr
strTy = TCon (TypeName "Str") []

mkMonoid :: Either Text Doctrine
mkMonoid = do
  let mt = ModeTheory (S.singleton modeM) M.empty []
  let types = M.fromList [(modeM, M.fromList [(TypeName "A", 0)])]
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
  let types = M.fromList [(modeM, M.fromList [(TypeName "Str", 0)])]
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
