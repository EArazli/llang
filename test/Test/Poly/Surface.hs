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
    , testCase "surface rejects binder type in wrong mode" testSurfaceBinderModeMismatch
    , testCase "surface affine rejects duplication" testSurfaceAffineRejectsDup
    , testCase "surface relevant rejects drop" testSurfaceRelevantRejectsDrop
    , testCase "surface linear rejects duplication" testSurfaceLinearRejectsDup
    , testCase "surface linear rejects drop" testSurfaceLinearRejectsDrop
    , testCase "surface uses configured dup generator" testSurfaceCustomDup
    , testCase "surface uses configured drop generator" testSurfaceCustomDrop
    ]


specText :: Text
specText =
  specTextWithStructural []

specTextWithStructural :: [Text] -> Text
specTextWithStructural structuralLines =
  T.unlines
    ( [ "doctrine TestDoc;"
      , "mode M;"
      ]
        <> structuralLines
        <> [ "lexer {"
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
    )

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
        , gdAttrs = []
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
      , dAttrSorts = M.empty
      }

mkDoctrineWithExtraMode :: Doctrine
mkDoctrineWithExtraMode =
  let modeM = ModeName "M"
      modeC = ModeName "C"
      a = TypeName "A"
      tyA = TCon (TypeRef modeM a) []
      aVar = TyVar { tvName = "a", tvMode = modeM }
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
      genF = mkGen "f" [] [tyA, tyA] [tyA]
      genUnit = mkGen "unit" [] [] [tyA]
      gens = M.fromList
        [ (GenName "dup", genDup)
        , (GenName "drop", genDrop)
        , (GenName "f", genF)
        , (GenName "unit", genUnit)
        ]
  in Doctrine
      { dName = "TestDoc"
      , dModes = ModeTheory (S.fromList [modeM, modeC]) M.empty []
      , dTypes = M.fromList
          [ (modeM, M.fromList [(a, TypeSig [])])
          , (modeC, M.fromList [(a, TypeSig [])])
          ]
      , dGens = M.fromList [(modeM, gens)]
      , dCells2 = []
      , dAttrSorts = M.empty
      }

mkSurface :: Either Text (Doctrine, PolySurfaceDef)
mkSurface = do
  spec <- parseSurfaceSpec specText
  def <- elabPolySurfaceDecl "TestSurface" mkDoctrine spec
  pure (mkDoctrine, def)

mkSurfaceWithSpec :: Text -> Doctrine -> Either Text PolySurfaceDef
mkSurfaceWithSpec specText' doc = do
  spec <- parseSurfaceSpec specText'
  elabPolySurfaceDecl "TestSurface" doc spec

assertHasGen :: Text -> Diagram -> Assertion
assertHasGen name diag =
  let payloads = [ g | Edge _ (PGen g _) _ _ <- IM.elems (dEdges diag) ]
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

testSurfaceBinderModeMismatch :: Assertion
testSurfaceBinderModeMismatch = do
  surf <- case mkSurfaceWithSpec specText mkDoctrineWithExtraMode of
    Left err -> assertFailure (T.unpack err)
    Right s -> pure s
  let expr = T.unlines
        [ "term {"
        , "  in x:C.A;"
        , "  out x"
        , "}"
        ]
  case elabSurfaceExpr mkDoctrineWithExtraMode surf expr of
    Left err ->
      assertBool "expected binder mode mismatch" ("binder type must be in surface mode" `T.isInfixOf` err)
    Right _ -> assertFailure "expected binder mode mismatch error"

testSurfaceAffineRejectsDup :: Assertion
testSurfaceAffineRejectsDup = do
  let specTextAffine =
        specTextWithStructural
          [ "structural {"
          , "  discipline: affine;"
          , "  drop: drop;"
          , "}"
          ]
  surf <- case mkSurfaceWithSpec specTextAffine mkDoctrine of
    Left err -> assertFailure (T.unpack err)
    Right s -> pure s
  let expr = T.unlines
        [ "term {"
        , "  in x:A;"
        , "  out f(x, x)"
        , "}"
        ]
  case elabSurfaceExpr mkDoctrine surf expr of
    Left err ->
      assertBool "expected affine duplication error" ("duplicated" `T.isInfixOf` err && "affine" `T.isInfixOf` err)
    Right _ -> assertFailure "expected affine duplication error"

testSurfaceRelevantRejectsDrop :: Assertion
testSurfaceRelevantRejectsDrop = do
  let specTextRelevant =
        specTextWithStructural
          [ "structural {"
          , "  discipline: relevant;"
          , "  dup: dup;"
          , "}"
          ]
  surf <- case mkSurfaceWithSpec specTextRelevant mkDoctrine of
    Left err -> assertFailure (T.unpack err)
    Right s -> pure s
  let expr = T.unlines
        [ "term {"
        , "  in x:A;"
        , "  out unit"
        , "}"
        ]
  case elabSurfaceExpr mkDoctrine surf expr of
    Left err ->
      assertBool "expected relevant drop error" ("dropped" `T.isInfixOf` err && "relevant" `T.isInfixOf` err)
    Right _ -> assertFailure "expected relevant drop error"

testSurfaceLinearRejectsDup :: Assertion
testSurfaceLinearRejectsDup = do
  let specTextLinear =
        specTextWithStructural
          [ "structural {"
          , "  discipline: linear;"
          , "}"
          ]
  surf <- case mkSurfaceWithSpec specTextLinear mkDoctrine of
    Left err -> assertFailure (T.unpack err)
    Right s -> pure s
  let expr = T.unlines
        [ "term {"
        , "  in x:A;"
        , "  out f(x, x)"
        , "}"
        ]
  case elabSurfaceExpr mkDoctrine surf expr of
    Left err ->
      assertBool "expected linear duplication error" ("duplicated" `T.isInfixOf` err && "linear" `T.isInfixOf` err)
    Right _ -> assertFailure "expected linear duplication error"

testSurfaceLinearRejectsDrop :: Assertion
testSurfaceLinearRejectsDrop = do
  let specTextLinear =
        specTextWithStructural
          [ "structural {"
          , "  discipline: linear;"
          , "}"
          ]
  surf <- case mkSurfaceWithSpec specTextLinear mkDoctrine of
    Left err -> assertFailure (T.unpack err)
    Right s -> pure s
  let expr = T.unlines
        [ "term {"
        , "  in x:A;"
        , "  out unit"
        , "}"
        ]
  case elabSurfaceExpr mkDoctrine surf expr of
    Left err ->
      assertBool "expected linear drop error" ("dropped" `T.isInfixOf` err && "linear" `T.isInfixOf` err)
    Right _ -> assertFailure "expected linear drop error"

mkDoctrineCustom :: Doctrine
mkDoctrineCustom =
  let mode = ModeName "M"
      a = TypeName "A"
      tyA = TCon (TypeRef mode a) []
      aVar = TyVar { tvName = "a", tvMode = mode }
      mkGen name tyVars dom cod = GenDecl
        { gdName = GenName name
        , gdMode = mode
        , gdTyVars = tyVars
        , gdDom = dom
        , gdCod = cod
        , gdAttrs = []
        }
      genCopy = mkGen "copy" [aVar] [TVar aVar] [TVar aVar, TVar aVar]
      genDiscard = mkGen "discard" [aVar] [TVar aVar] []
      genF = mkGen "f" [] [tyA, tyA] [tyA]
      genUnit = mkGen "unit" [] [] [tyA]
      gens = M.fromList
        [ (GenName "copy", genCopy)
        , (GenName "discard", genDiscard)
        , (GenName "f", genF)
        , (GenName "unit", genUnit)
        ]
  in Doctrine
      { dName = "TestDoc"
      , dModes = ModeTheory (S.singleton mode) M.empty []
      , dTypes = M.fromList [(mode, M.fromList [(a, TypeSig [])])]
      , dGens = M.fromList [(mode, gens)]
      , dCells2 = []
      , dAttrSorts = M.empty
      }

testSurfaceCustomDup :: Assertion
testSurfaceCustomDup = do
  let specTextCustom =
        specTextWithStructural
          [ "structural {"
          , "  discipline: cartesian;"
          , "  dup: copy;"
          , "  drop: discard;"
          , "}"
          ]
  surf <- case mkSurfaceWithSpec specTextCustom mkDoctrineCustom of
    Left err -> assertFailure (T.unpack err)
    Right s -> pure s
  let expr = T.unlines
        [ "term {"
        , "  in x:A;"
        , "  out f(x, x)"
        , "}"
        ]
  case elabSurfaceExpr mkDoctrineCustom surf expr of
    Left err -> assertFailure (T.unpack err)
    Right diag -> assertHasGen "copy" diag

testSurfaceCustomDrop :: Assertion
testSurfaceCustomDrop = do
  let specTextCustom =
        specTextWithStructural
          [ "structural {"
          , "  discipline: cartesian;"
          , "  dup: copy;"
          , "  drop: discard;"
          , "}"
          ]
  surf <- case mkSurfaceWithSpec specTextCustom mkDoctrineCustom of
    Left err -> assertFailure (T.unpack err)
    Right s -> pure s
  let expr = T.unlines
        [ "term {"
        , "  in x:A;"
        , "  out unit"
        , "}"
        ]
  case elabSurfaceExpr mkDoctrineCustom surf expr of
    Left err -> assertFailure (T.unpack err)
    Right diag -> assertHasGen "discard" diag
