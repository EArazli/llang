{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Surface
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM

import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..), TyVar(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..))
import Strat.Poly.Surface.Parse (parseSurfaceSpec)
import Strat.Poly.Surface (PolySurfaceDef, elabPolySurfaceDecl)
import Strat.Poly.Surface.Elab (elabSurfaceExpr)
import Strat.Poly.Graph (Diagram(..), Edge(..), EdgePayload(..))


tests :: TestTree
tests =
  testGroup
    "Poly.Surface"
    [ testCase "surface parse/elab ok" testSurfaceElabOk
    , testCase "surface inserts dup for multiple uses" testSurfaceDup
    , testCase "surface inserts drop for unused" testSurfaceDrop
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

mkDoctrine :: Doctrine
mkDoctrine =
  let mode = ModeName "M"
      a = TypeName "A"
      tyA = TCon (TypeRef mode a) []
      aVar = TyVar { tvName = "a", tvMode = mode }
      bVar = TyVar { tvName = "b", tvMode = mode }
      mkGen name tyVars dom cod = GenDecl
        { gdName = GenName name
        , gdMode = mode
        , gdTyVars = tyVars
        , gdDom = dom
        , gdCod = cod
        }
      genDup = mkGen "dup" [aVar] [TVar aVar] [TVar aVar, TVar aVar]
      genDrop = mkGen "drop" [aVar] [TVar aVar] []
      genSwap = mkGen "swap" [aVar, bVar] [TVar aVar, TVar bVar] [TVar bVar, TVar aVar]
      genF = mkGen "f" [] [tyA, tyA] [tyA]
      genUnit = mkGen "unit" [] [] [tyA]
      gens = M.fromList
        [ (GenName "dup", genDup)
        , (GenName "drop", genDrop)
        , (GenName "swap", genSwap)
        , (GenName "f", genF)
        , (GenName "unit", genUnit)
        ]
  in Doctrine
      { dName = "TestDoc"
      , dModes = ModeTheory (S.singleton mode) M.empty []
      , dTypes = M.fromList [(mode, M.fromList [(a, TypeSig [])])]
      , dGens = M.fromList [(mode, gens)]
      , dCells2 = []
      }

mkSurface :: Either Text (Doctrine, PolySurfaceDef)
mkSurface = do
  spec <- parseSurfaceSpec specText
  def <- elabPolySurfaceDecl "TestSurface" mkDoctrine spec
  pure (mkDoctrine, def)

assertHasGen :: Text -> Diagram -> Assertion
assertHasGen name diag =
  let payloads = [ g | Edge _ (PGen g) _ _ <- IM.elems (dEdges diag) ]
  in if GenName name `elem` payloads then pure () else assertFailure ("expected gen " <> T.unpack name)


testSurfaceElabOk :: Assertion
testSurfaceElabOk = do
  (doc, surf) <- either (assertFailure . T.unpack) pure mkSurface
  let expr = T.unlines
        [ "term {"
        , "  in x:A;"
        , "  out x"
        , "}"
        ]
  case elabSurfaceExpr doc surf expr of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()


testSurfaceDup :: Assertion
testSurfaceDup = do
  (doc, surf) <- either (assertFailure . T.unpack) pure mkSurface
  let expr = T.unlines
        [ "term {"
        , "  in x:A;"
        , "  out f(x, x)"
        , "}"
        ]
  case elabSurfaceExpr doc surf expr of
    Left err -> assertFailure (T.unpack err)
    Right diag -> assertHasGen "dup" diag


testSurfaceDrop :: Assertion
testSurfaceDrop = do
  (doc, surf) <- either (assertFailure . T.unpack) pure mkSurface
  let expr = T.unlines
        [ "term {"
        , "  in x:A;"
        , "  out unit"
        , "}"
        ]
  case elabSurfaceExpr doc surf expr of
    Left err -> assertFailure (T.unpack err)
    Right diag -> assertHasGen "drop" diag
