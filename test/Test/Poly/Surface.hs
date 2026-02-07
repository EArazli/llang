{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Surface
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import Strat.Frontend.Env (emptyEnv, ModuleEnv(..), TermDef(..))
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..), ModeInfo(..), VarDiscipline(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..), TyVar(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..))
import Strat.Poly.Surface.Parse (parseSurfaceSpec)
import Strat.Poly.Surface (PolySurfaceDef, elabPolySurfaceDecl)
import Strat.Poly.Surface.Elab (elabSurfaceExpr)
import Strat.Poly.Diagram (idD)
import Strat.Poly.Graph (Diagram(..), Edge(..), EdgePayload(..), diagramIsoEq)
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.Surface"
    [ testCase "surface parse/elab ok" testSurfaceElabOk
    , testCase "surface inserts dup for multiple uses" testSurfaceDup
    , testCase "surface inserts drop for unused" testSurfaceDrop
    , testCase "surface affine rejects duplication" testSurfaceAffineRejectsDup
    , testCase "surface relevant rejects drop" testSurfaceRelevantRejectsDrop
    , testCase "surface linear rejects duplication and drop" testSurfaceLinearRejectsBoth
    , testCase "template @TermName splice uses module term" testSurfaceTemplateSplice
    ]


specText :: Text
specText =
  T.unlines
    [ "doctrine TestDoc;"
    , "mode M;"
    , "lexer {"
    , "  keywords: term, in, out;"
    , "  symbols: \"(\", \")\", \"{\", \"}\", \":\", \";\", \",\";"
    , "}"
    , "expr {"
    , "  atom:"
    , "    ident \"(\" <expr> \")\" => CALL(name, args)"
    , "  | ident => VAR(name)"
    , "  | \"out\" <expr> => OUT(expr)"
    , "  | \"term\" \"{\" <expr> \"}\" => DIAG(expr)"
    , "  | \"(\" <expr> \")\" => <expr>"
    , "  ;"
    , "  prefix:"
    , "    \"in\" ident \":\" <type> \";\" <expr> => IN(name, ty, body)"
    , "  ;"
    , "  infixr 10 \",\" => LIST(lhs, rhs);"
    , "}"
    , "elaborate {"
    , "  VAR(x) => $x;;"
    , "  LIST(a, b) => $1 * $2;;"
    , "  OUT(e) => $1;;"
    , "  DIAG(e) => $1;;"
    , "  IN(x, ty, body) => $1;;"
    , "}"
    ]

spliceSpecText :: Text
spliceSpecText =
  T.unlines
    [ "doctrine TestDoc;"
    , "mode M;"
    , "lexer {"
    , "  keywords: use;"
    , "  symbols: ;"
    , "}"
    , "expr {"
    , "  atom: \"use\" => USE();"
    , "}"
    , "elaborate {"
    , "  USE() => @T;;"
    , "}"
    ]

modeM :: ModeName
modeM = ModeName "M"

typeA :: TypeExpr
typeA = TCon (TypeRef modeM (TypeName "A")) []

mkDoctrineWithDiscipline :: VarDiscipline -> Doctrine
mkDoctrineWithDiscipline disc =
  let aVar = TyVar { tvName = "a", tvMode = modeM }
      mkGen name tyVars dom cod = GenDecl
        { gdName = GenName name
        , gdMode = modeM
        , gdTyVars = tyVars
        , gdDom = dom
        , gdCod = cod
        , gdAttrs = []
        }
      genDup = mkGen "dup" [aVar] [TVar aVar] [TVar aVar, TVar aVar]
      genDrop = mkGen "drop" [aVar] [TVar aVar] []
      genF = mkGen "f" [] [typeA, typeA] [typeA]
      genUnit = mkGen "unit" [] [] [typeA]
      mt0 = mkModes [modeM]
      mt = mt0 { mtModes = M.singleton modeM (ModeInfo modeM disc) }
  in Doctrine
      { dName = "TestDoc"
      , dModes = mt
      , dTypes = M.fromList [(modeM, M.fromList [(TypeName "A", TypeSig [])])]
      , dGens =
          M.fromList
            [ ( modeM
              , M.fromList
                  [ (GenName "dup", genDup)
                  , (GenName "drop", genDrop)
                  , (GenName "f", genF)
                  , (GenName "unit", genUnit)
                  ]
              )
            ]
      , dCells2 = []
      , dAttrSorts = M.empty
      }

mkSurfaceWithSpec :: Text -> Doctrine -> Either Text PolySurfaceDef
mkSurfaceWithSpec txt doc = do
  spec <- parseSurfaceSpec txt
  elabPolySurfaceDecl "TestSurface" doc spec

assertHasGen :: Text -> Diagram -> Assertion
assertHasGen name diag =
  let payloads = [ g | Edge _ (PGen g _) _ _ <- IM.elems (dEdges diag) ]
  in if GenName name `elem` payloads then pure () else assertFailure ("expected gen " <> T.unpack name)

testSurfaceElabOk :: Assertion
testSurfaceElabOk = do
  let doc = mkDoctrineWithDiscipline Cartesian
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out x", "}" ]
  case elabSurfaceExpr emptyEnv doc surf expr of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testSurfaceDup :: Assertion
testSurfaceDup = do
  let doc = mkDoctrineWithDiscipline Cartesian
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out f(x, x)", "}" ]
  case elabSurfaceExpr emptyEnv doc surf expr of
    Left err -> assertFailure (T.unpack err)
    Right diag -> assertHasGen "dup" diag

testSurfaceDrop :: Assertion
testSurfaceDrop = do
  let doc = mkDoctrineWithDiscipline Cartesian
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out unit", "}" ]
  case elabSurfaceExpr emptyEnv doc surf expr of
    Left err -> assertFailure (T.unpack err)
    Right diag -> assertHasGen "drop" diag

testSurfaceAffineRejectsDup :: Assertion
testSurfaceAffineRejectsDup = do
  let doc = mkDoctrineWithDiscipline Affine
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out f(x, x)", "}" ]
  case elabSurfaceExpr emptyEnv doc surf expr of
    Left err ->
      assertBool "expected affine duplication error" ("duplicated" `T.isInfixOf` err && "affine" `T.isInfixOf` err)
    Right _ -> assertFailure "expected affine duplication error"

testSurfaceRelevantRejectsDrop :: Assertion
testSurfaceRelevantRejectsDrop = do
  let doc = mkDoctrineWithDiscipline Relevant
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out unit", "}" ]
  case elabSurfaceExpr emptyEnv doc surf expr of
    Left err ->
      assertBool "expected relevant drop error" ("dropped" `T.isInfixOf` err && "relevant" `T.isInfixOf` err)
    Right _ -> assertFailure "expected relevant drop error"

testSurfaceLinearRejectsBoth :: Assertion
testSurfaceLinearRejectsBoth = do
  let doc = mkDoctrineWithDiscipline Linear
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let dupExpr = T.unlines [ "term {", "  in x:A;", "  out f(x, x)", "}" ]
  case elabSurfaceExpr emptyEnv doc surf dupExpr of
    Left err ->
      assertBool "expected linear duplication error" ("duplicated" `T.isInfixOf` err && "linear" `T.isInfixOf` err)
    Right _ -> assertFailure "expected linear duplication error"
  let dropExpr = T.unlines [ "term {", "  in x:A;", "  out unit", "}" ]
  case elabSurfaceExpr emptyEnv doc surf dropExpr of
    Left err ->
      assertBool "expected linear drop error" ("dropped" `T.isInfixOf` err && "linear" `T.isInfixOf` err)
    Right _ -> assertFailure "expected linear drop error"

testSurfaceTemplateSplice :: Assertion
testSurfaceTemplateSplice = do
  let doc = mkDoctrineWithDiscipline Linear
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec spliceSpecText doc)
  let termDiag = idD modeM [typeA]
  let env =
        emptyEnv
          { meTerms =
              M.fromList
                [ ("T", TermDef { tdDoctrine = "TestDoc", tdMode = modeM, tdDiagram = termDiag })
                ]
          }
  out <- either (assertFailure . T.unpack) pure (elabSurfaceExpr env doc surf "use")
  iso <- case diagramIsoEq out termDiag of
    Left err -> assertFailure (T.unpack err)
    Right ok -> pure ok
  assertBool "expected spliced term diagram" iso
