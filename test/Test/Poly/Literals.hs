{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Literals
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (ModuleEnv(..), emptyEnv)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr
import Strat.Poly.Doctrine (Doctrine)
import Strat.Poly.Graph (Diagram(..), Edge(..), EdgePayload(..))
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Poly.Surface.Elab (elabSurfaceExpr)
import Strat.Poly.Surface (PolySurfaceDef)
import Strat.Poly.Rewrite (rulesFromDoctrine)
import Strat.Poly.Normalize (normalize, NormalizationStatus(..))
import Strat.Poly.Morphism (Morphism, checkMorphism, applyMorphismDiagram)
import Strat.Poly.Eval (evalDiagram)
import Strat.Poly.CriticalPairs (CPMode(..), CriticalPairInfo(..), CriticalPair(..), criticalPairsForDoctrine)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Model.Spec (ModelSpec)
import Strat.Backend (Value(..))


tests :: TestTree
tests =
  testGroup
    "Poly.Literals"
    [ testCase "attr substitution and unification basics" testAttrCore
    , testCase "parse/elab generator attributes named and positional" testParseElabGenAttrs
    , testCase "surface int capture injects attribute with #hole" testSurfaceLiteralCapture
    , testCase "rewrite substitutes matched attributes on RHS" testRewriteAttrSubstitution
    , testCase "morphism instantiates mapped generator attributes" testMorphismAttrInstantiation
    , testCase "evaluation passes attributes before wire args" testEvalAttrArgs
    , testCase "critical pairs respect attribute unification" testCriticalPairsAttrUnification
    ]


testAttrCore :: Assertion
testAttrCore = do
  let intSort = AttrSort "Int"
  let x = AttrVar "x" intSort
  let y = AttrVar "y" intSort
  let s1 = M.fromList [(x, ATVar y)]
  let s2 = M.fromList [(y, ATLit (ALInt 5))]
  let composed = composeAttrSubst s2 s1
  applyAttrSubstTerm composed (ATVar x) @?= ATLit (ALInt 5)
  applyAttrSubstTerm composed (ATVar y) @?= ATLit (ALInt 5)
  let u1 = unifyAttrFlex (S.singleton x) M.empty (ATVar x) (ATLit (ALInt 3))
  u1' <- require u1
  u1' @?= M.fromList [(x, ATLit (ALInt 3))]
  case unifyAttrFlex S.empty M.empty (ATVar x) (ATLit (ALInt 3)) of
    Left _ -> pure ()
    Right _ -> assertFailure "expected rigid variable mismatch"

testParseElabGenAttrs :: Assertion
testParseElabGenAttrs = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  attrsort Int = int;"
        , "  type A @M;"
        , "  gen Lit {n:Int} : [] -> [A] @M;"
        , "}"
        ]
  env <- require (elabSource src)
  doc <- lookupDoctrine "D" env
  named <- require (elabDiag doc "Lit(n=42)")
  positional <- require (elabDiag doc "Lit(42)")
  namedPayload <- require (singleGenPayload named)
  posPayload <- require (singleGenPayload positional)
  namedPayload @?= (GenName "Lit", M.fromList [("n", ATLit (ALInt 42))])
  posPayload @?= namedPayload

testSurfaceLiteralCapture :: Assertion
testSurfaceLiteralCapture = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  attrsort Int = int;"
        , "  type A @M;"
        , "  gen Lit {n:Int} : [] -> [A] @M;"
        , "}"
        , "surface NumLit where {"
        , "  doctrine D;"
        , "  mode M;"
        , "  structural {"
        , "    discipline: linear;"
        , "  }"
        , "  lexer {"
        , "    keywords: ;"
        , "    symbols: ;"
        , "  }"
        , "  expr {"
        , "    atom:"
        , "      int => LIT(n)"
        , "    ;"
        , "  }"
        , "  elaborate {"
        , "    LIT(n) => Lit(n=#n);;"
        , "  }"
        , "}"
        ]
  env <- require (elabSource src)
  doc <- lookupDoctrine "D" env
  surf <- lookupSurface "NumLit" env
  diag <- require (elabSurfaceExpr doc surf "42")
  payload <- require (singleGenPayload diag)
  payload @?= (GenName "Lit", M.fromList [("n", ATLit (ALInt 42))])

testRewriteAttrSubstitution :: Assertion
testRewriteAttrSubstitution = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  attrsort Int = int;"
        , "  type A @M;"
        , "  gen IdLit {n:Int} : [] -> [A] @M;"
        , "  gen Lit {n:Int} : [] -> [A] @M;"
        , "  rule computational simplify -> : [] -> [A] @M ="
        , "    IdLit(n) == Lit(n)"
        , "}"
        ]
  env <- require (elabSource src)
  doc <- lookupDoctrine "D" env
  diag <- require (elabDiag doc "IdLit(7)")
  norm <- require (normalize 10 (rulesFromDoctrine doc) diag)
  out <- case norm of
    Finished d -> pure d
    OutOfFuel _ -> assertFailure "expected rewrite to normalize within fuel" >> pure diag
  payload <- require (singleGenPayload out)
  payload @?= (GenName "Lit", M.fromList [("n", ATLit (ALInt 7))])

testMorphismAttrInstantiation :: Assertion
testMorphismAttrInstantiation = do
  let src = T.unlines
        [ "doctrine Src where {"
        , "  mode M;"
        , "  attrsort Int = int;"
        , "  type A @M;"
        , "  gen Lit {n:Int} : [] -> [A] @M;"
        , "}"
        , "doctrine Tgt where {"
        , "  mode M;"
        , "  attrsort Int = int;"
        , "  type B @M;"
        , "  gen Lit2 {n:Int} : [] -> [B] @M;"
        , "}"
        , "morphism LitMap : Src -> Tgt where {"
        , "  mode M -> M;"
        , "  attrsort Int -> Int;"
        , "  type A @M -> B @M;"
        , "  gen Lit @M -> Lit2(n=n)"
        , "}"
        ]
  env <- require (elabSource src)
  doc <- lookupDoctrine "Src" env
  mor <- lookupMorphism "LitMap" env
  require (checkMorphism mor)
  diag <- require (elabDiag doc "Lit(5)")
  mapped <- require (applyMorphismDiagram mor diag)
  payload <- require (singleGenPayload mapped)
  payload @?= (GenName "Lit2", M.fromList [("n", ATLit (ALInt 5))])

testEvalAttrArgs :: Assertion
testEvalAttrArgs = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  attrsort Int = int;"
        , "  type A @M;"
        , "  gen Lit {n:Int} : [] -> [A] @M;"
        , "}"
        , "model Eval : D where {"
        , "  default = error \"missing op\";"
        , "  op Lit(n) = n;"
        , "}"
        ]
  env <- require (elabSource src)
  doc <- lookupDoctrine "D" env
  model <- lookupModel "Eval" env
  diag <- require (elabDiag doc "Lit(13)")
  vals <- require (evalDiagram doc model diag [])
  vals @?= [VInt 13]

testCriticalPairsAttrUnification :: Assertion
testCriticalPairsAttrUnification = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  attrsort Int = int;"
        , "  type A @M;"
        , "  gen IdLit {n:Int} : [] -> [A] @M;"
        , "  gen Lit {n:Int} : [] -> [A] @M;"
        , "  rule computational r1 -> : [] -> [A] @M ="
        , "    IdLit(1) == Lit(1)"
        , "  rule computational r2 -> : [] -> [A] @M ="
        , "    IdLit(2) == Lit(2)"
        , "}"
        ]
  env <- require (elabSource src)
  doc <- lookupDoctrine "D" env
  pairs <- require (criticalPairsForDoctrine CP_All UseAllOriented doc)
  let cross =
        [ cpiPair info
        | info <- pairs
        , let a = cpRule1 (cpiPair info)
        , let b = cpRule2 (cpiPair info)
        , ("r1" `T.isPrefixOf` a && "r2" `T.isPrefixOf` b) || ("r2" `T.isPrefixOf` a && "r1" `T.isPrefixOf` b)
        ]
  assertBool "expected no cross-rule overlaps for mismatched attribute literals" (null cross)


elabSource :: T.Text -> Either T.Text ModuleEnv
elabSource src = do
  raw <- parseRawFile src
  elabRawFile raw

lookupDoctrine :: T.Text -> ModuleEnv -> IO Doctrine
lookupDoctrine name env =
  case M.lookup name (meDoctrines env) of
    Nothing -> assertFailure ("missing doctrine: " <> T.unpack name) >> fail "unreachable"
    Just doc -> pure doc

lookupSurface :: T.Text -> ModuleEnv -> IO PolySurfaceDef
lookupSurface name env =
  case M.lookup name (meSurfaces env) of
    Nothing -> assertFailure ("missing surface: " <> T.unpack name) >> fail "unreachable"
    Just surf -> pure surf

lookupMorphism :: T.Text -> ModuleEnv -> IO Morphism
lookupMorphism name env =
  case M.lookup name (meMorphisms env) of
    Nothing -> assertFailure ("missing morphism: " <> T.unpack name) >> fail "unreachable"
    Just mor -> pure mor

lookupModel :: T.Text -> ModuleEnv -> IO ModelSpec
lookupModel name env =
  case M.lookup name (meModels env) of
    Nothing -> assertFailure ("missing model: " <> T.unpack name) >> fail "unreachable"
    Just (_, model) -> pure model

elabDiag :: Doctrine -> T.Text -> Either T.Text Diagram
elabDiag doc src = do
  raw <- parseDiagExpr src
  elabDiagExpr emptyEnv doc (ModeName "M") [] raw

singleGenPayload :: Diagram -> Either T.Text (GenName, AttrMap)
singleGenPayload diag =
  case IM.elems (dEdges diag) of
    [Edge _ (PGen g attrs) _ _] -> Right (g, attrs)
    _ -> Left "expected diagram with exactly one generator edge"

require :: Either T.Text a -> IO a
require = either (assertFailure . T.unpack) pure
