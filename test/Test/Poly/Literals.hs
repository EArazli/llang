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
import Strat.Poly.Doctrine (Doctrine(..), validateDoctrine)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Graph (Diagram(..), Edge(..), EdgePayload(..))
import Strat.Poly.Diagram (renameAttrVarsDiagram)
import Strat.Poly.DSL.Parse (parseDiagExpr)
import qualified Strat.Poly.DSL.AST as PolyAST
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
    , testCase "critical pairs freshen attribute variables across rules" testCriticalPairsFreshenAttrVars
    , testCase "morphism rejects attrsort mapping across literal kinds" testMorphismRejectsAttrKindChange
    , testCase "surface rejects direct calls to attribute-bearing generators" testSurfaceRejectsDirectAttrGenCall
    , testCase "attribute parser treats truex as variable, not bool keyword" testAttrBoolKeywordBoundary
    , testCase "validateDoctrine rejects fresh attribute var introduced on RHS" testDoctrineRejectsFreshAttrVarOnRHS
    , testCase "surface rejects conflicting sorts for same attribute variable name" testSurfaceRejectsConflictingAttrVarSorts
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
  diag <- require (elabSurfaceExpr emptyEnv doc surf "42")
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

testCriticalPairsFreshenAttrVars :: Assertion
testCriticalPairsFreshenAttrVars = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  attrsort Int = int;"
        , "  type A @M;"
        , "  gen LitA {n:Int} : [] -> [A] @M;"
        , "  gen LitB {n:Int} : [] -> [A] @M;"
        , "  rule computational r1 -> : [] -> [A, A] @M ="
        , "    LitA(x) * LitB(y) == LitA(x) * LitB(y)"
        , "  rule computational r2 -> : [] -> [A] @M ="
        , "    LitA(y) == LitB(y)"
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
  assertBool "expected at least one cross-rule critical pair" (not (null cross))
  mapM_ checkPair cross
  where
    checkPair cp = do
      litA <- require (uniqueGenAttr (GenName "LitA") "n" (cpOverlap cp))
      litB <- require (uniqueGenAttr (GenName "LitB") "n" (cpOverlap cp))
      case (litA, litB) of
        (ATVar varA, ATVar varB) ->
          assertBool "expected LitA.n and LitB.n to remain distinct after overlap freshening" (varA /= varB)
        _ ->
          assertFailure "expected LitA.n and LitB.n to be attribute variables"

testMorphismRejectsAttrKindChange :: Assertion
testMorphismRejectsAttrKindChange = do
  let src = T.unlines
        [ "doctrine Src where {"
        , "  mode M;"
        , "  attrsort I = int;"
        , "  type A @M;"
        , "  gen Lit {n:I} : [] -> [A] @M;"
        , "}"
        , "doctrine Tgt where {"
        , "  mode M;"
        , "  attrsort S = string;"
        , "  type A @M;"
        , "  gen Lit {n:S} : [] -> [A] @M;"
        , "}"
        , "morphism Bad : Src -> Tgt where {"
        , "  mode M -> M;"
        , "  attrsort I -> S;"
        , "  type A @M -> A @M;"
        , "  gen Lit @M -> Lit(n=n)"
        , "}"
        ]
  case elabSource src of
    Left err ->
      assertBool
        "expected literal-kind mismatch in attrsort mapping"
        ("attrsort mapping changes literal kind" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected morphism elaboration to fail"

testSurfaceRejectsDirectAttrGenCall :: Assertion
testSurfaceRejectsDirectAttrGenCall = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  attrsort Int = int;"
        , "  type A @M;"
        , "  gen Lit {n:Int} : [] -> [A] @M;"
        , "}"
        , "surface S where {"
        , "  doctrine D;"
        , "  mode M;"
        , "  lexer {"
        , "    keywords: ;"
        , "    symbols: ;"
        , "  }"
        , "  expr {"
        , "    atom:"
        , "      ident => REF(name)"
        , "    ;"
        , "  }"
        , "  elaborate {"
        , "    REF(name) => $name;;"
        , "  }"
        , "}"
        ]
  env <- require (elabSource src)
  doc <- lookupDoctrine "D" env
  surf <- lookupSurface "S" env
  case elabSurfaceExpr emptyEnv doc surf "Lit" of
    Left err ->
      assertBool
        "expected explicit rejection for attribute-bearing direct generator calls"
        ("generator requires attribute arguments" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected surface elaboration failure"

testAttrBoolKeywordBoundary :: Assertion
testAttrBoolKeywordBoundary = do
  raw <- require (parseDiagExpr "Lit(truex)")
  case raw of
    PolyAST.RDGen "Lit" Nothing (Just [PolyAST.RAPos (PolyAST.RATVar name)]) ->
      name @?= "truex"
    _ ->
      assertFailure "expected Lit(truex) to parse with attribute variable truex"

testDoctrineRejectsFreshAttrVarOnRHS :: Assertion
testDoctrineRejectsFreshAttrVarOnRHS = do
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
  case dCells2 doc of
    [] -> assertFailure "expected at least one doctrine cell"
    (cell0:rest) -> do
      let rhs' = renameAttrVarsDiagram (const "m") (c2RHS cell0)
      let doc' = doc { dCells2 = cell0 { c2RHS = rhs' } : rest }
      case validateDoctrine doc' of
        Left err ->
          assertBool
            "expected doctrine validation to reject fresh RHS attribute vars"
            ("fresh attribute variables" `T.isInfixOf` err)
        Right () ->
          assertFailure "expected validateDoctrine to fail"

testSurfaceRejectsConflictingAttrVarSorts :: Assertion
testSurfaceRejectsConflictingAttrVarSorts = do
  let src = T.unlines
        [ "doctrine D where {"
        , "  mode M;"
        , "  attrsort Int = int;"
        , "  attrsort Bool = bool;"
        , "  type A @M;"
        , "  gen GI {n:Int} : [] -> [A] @M;"
        , "  gen GB {n:Bool} : [] -> [A] @M;"
        , "}"
        , "surface S where {"
        , "  doctrine D;"
        , "  mode M;"
        , "  lexer {"
        , "    keywords: ;"
        , "    symbols: ;"
        , "  }"
        , "  expr {"
        , "    atom:"
        , "      \"u\" => MIX"
        , "    ;"
        , "  }"
        , "  elaborate {"
        , "    MIX => GI(x) * GB(x);;"
        , "  }"
        , "}"
        ]
  env <- require (elabSource src)
  doc <- lookupDoctrine "D" env
  surf <- lookupSurface "S" env
  case elabSurfaceExpr emptyEnv doc surf "u" of
    Left err ->
      assertBool
        "expected conflicting attribute-variable sorts to be rejected"
        ("conflicting sorts" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected surface elaboration failure"


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

uniqueGenAttr :: GenName -> AttrName -> Diagram -> Either T.Text AttrTerm
uniqueGenAttr genName fieldName diag =
  case terms of
    [term] -> Right term
    [] -> Left "expected exactly one generator edge with the requested attribute"
    _ -> Left "expected unique generator attribute occurrence"
  where
    terms =
      [ term
      | Edge _ (PGen g attrs) _ _ <- IM.elems (dEdges diag)
      , g == genName
      , Just term <- [M.lookup fieldName attrs]
      ]

require :: Either T.Text a -> IO a
require = either (assertFailure . T.unpack) pure
