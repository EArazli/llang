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
import qualified Data.Set as S
import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (emptyEnv, ModuleEnv(..), TermDef(..))
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..), ModeInfo(..), VarDiscipline(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..), TyVar(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..), InputShape(..))
import Strat.Poly.Surface.Parse (parseSurfaceSpec)
import Strat.Poly.Surface (PolySurfaceDef, elabPolySurfaceDecl)
import Strat.Poly.Surface.Elab (elabSurfaceExpr)
import Strat.Poly.Diagram (idD, diagramDom, diagramCod)
import Strat.Poly.Graph (Diagram(..), Edge(..), EdgePayload(..), diagramIsoEq)
import Test.Poly.Helpers (mkModes)


tests :: TestTree
tests =
  testGroup
    "Poly.Surface"
    [ testCase "surface parse/elab ok" testSurfaceElabOk
    , testCase "surface inserts dup for multiple uses" testSurfaceDup
    , testCase "surface dup chain is left-associated for 3 uses" testSurfaceDupLeftAssociated
    , testCase "surface inserts drop for unused" testSurfaceDrop
    , testCase "surface affine rejects duplication" testSurfaceAffineRejectsDup
    , testCase "surface relevant rejects drop" testSurfaceRelevantRejectsDrop
    , testCase "surface linear rejects duplication and drop" testSurfaceLinearRejectsBoth
    , testCase "surface composition unifies through mode equations" testSurfaceModeEqComp
    , testCase "template @TermName splice uses module term" testSurfaceTemplateSplice
    , testCase "surface elaboration eliminates to base doctrine" testSurfaceEliminatesToBaseDoctrine
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
    , "    ident(name) \"(\" <expr> \")\" => $1 ; #name"
    , "  | ident(name) => $name"
    , "  | \"out\" <expr> => $1"
    , "  | \"term\" \"{\" <expr> \"}\" => $1"
    , "  | \"(\" <expr> \")\" => <expr>"
    , "  ;"
    , "  prefix:"
    , "    \"in\" ident(name) \":\" <type>(ty) \";\" <expr> => <expr> bind in(name, ty, 1)"
    , "  ;"
    , "  infixr 10 \",\" => $1 * $2;"
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
    , "  atom: \"use\" => @T;"
    , "}"
    ]

modeM :: ModeName
modeM = ModeName "M"

typeA :: TypeExpr
typeA = TCon (TypeRef modeM (TypeName "A")) []

mkDoctrineWithDiscipline :: VarDiscipline -> Doctrine
mkDoctrineWithDiscipline disc =
  let aVar = TyVar { tvName = "a", tvMode = modeM }
      mkGen name tyVars dom cod =
        GenDecl
          { gdName = GenName name
          , gdMode = modeM
          , gdTyVars = tyVars
          , gdIxVars = []
          , gdDom = map InPort dom
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
        , dIndexModes = S.empty
        , dIxTheory = M.empty
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
  elabPolySurfaceDecl "TestSurface" doc Nothing spec

elabSurfaceDiagram :: ModuleEnv -> Doctrine -> PolySurfaceDef -> Text -> Either Text Diagram
elabSurfaceDiagram env doc surf expr =
  fmap snd (elabSurfaceExpr env doc surf expr)

assertHasGen :: Text -> Diagram -> Assertion
assertHasGen name diag =
  let payloads = [ g | Edge _ (PGen g _ _) _ _ <- IM.elems (dEdges diag) ]
   in if GenName name `elem` payloads then pure () else assertFailure ("expected gen " <> T.unpack name)

testSurfaceElabOk :: Assertion
testSurfaceElabOk = do
  let doc = mkDoctrineWithDiscipline Cartesian
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out x", "}" ]
  case elabSurfaceDiagram emptyEnv doc surf expr of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testSurfaceDup :: Assertion
testSurfaceDup = do
  let doc = mkDoctrineWithDiscipline Cartesian
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out f(x, x)", "}" ]
  case elabSurfaceDiagram emptyEnv doc surf expr of
    Left err -> assertFailure (T.unpack err)
    Right diag -> assertHasGen "dup" diag

testSurfaceDupLeftAssociated :: Assertion
testSurfaceDupLeftAssociated = do
  let doc = mkDoctrineWithDiscipline Cartesian
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out x, x, x", "}" ]
  diag <- either (assertFailure . T.unpack) pure (elabSurfaceDiagram emptyEnv doc surf expr)
  let dupEdges = [ e | e@(Edge _ (PGen g _ _) _ _) <- IM.elems (dEdges diag), g == GenName "dup" ]
  length dupEdges @?= 2
  inPort <-
    case dIn diag of
      [p] -> pure p
      _ -> assertFailure "expected exactly one input port for binder"
  firstDup <-
    case filter (\e -> eIns e == [inPort]) dupEdges of
      [e] -> pure e
      _ -> assertFailure "expected exactly one dup edge consuming binder input"
  o1 <-
    case eOuts firstDup of
      [p, _] -> pure p
      _ -> assertFailure "expected dup codomain to have arity 2"
  secondDup <-
    case filter (\e -> eId e /= eId firstDup) dupEdges of
      [e] -> pure e
      _ -> assertFailure "expected exactly one remaining dup edge"
  eIns secondDup @?= [o1]

testSurfaceDrop :: Assertion
testSurfaceDrop = do
  let doc = mkDoctrineWithDiscipline Cartesian
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out unit", "}" ]
  case elabSurfaceDiagram emptyEnv doc surf expr of
    Left err -> assertFailure (T.unpack err)
    Right diag -> assertHasGen "drop" diag

testSurfaceAffineRejectsDup :: Assertion
testSurfaceAffineRejectsDup = do
  let doc = mkDoctrineWithDiscipline Affine
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out f(x, x)", "}" ]
  case elabSurfaceDiagram emptyEnv doc surf expr of
    Left err ->
      assertBool "expected affine duplication error" ("duplicated" `T.isInfixOf` err && "affine" `T.isInfixOf` err)
    Right _ -> assertFailure "expected affine duplication error"

testSurfaceRelevantRejectsDrop :: Assertion
testSurfaceRelevantRejectsDrop = do
  let doc = mkDoctrineWithDiscipline Relevant
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out unit", "}" ]
  case elabSurfaceDiagram emptyEnv doc surf expr of
    Left err ->
      assertBool "expected relevant drop error" ("dropped" `T.isInfixOf` err && "relevant" `T.isInfixOf` err)
    Right _ -> assertFailure "expected relevant drop error"

testSurfaceLinearRejectsBoth :: Assertion
testSurfaceLinearRejectsBoth = do
  let doc = mkDoctrineWithDiscipline Linear
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let dupExpr = T.unlines [ "term {", "  in x:A;", "  out f(x, x)", "}" ]
  case elabSurfaceDiagram emptyEnv doc surf dupExpr of
    Left err ->
      assertBool "expected linear duplication error" ("duplicated" `T.isInfixOf` err && "linear" `T.isInfixOf` err)
    Right _ -> assertFailure "expected linear duplication error"
  let dropExpr = T.unlines [ "term {", "  in x:A;", "  out unit", "}" ]
  case elabSurfaceDiagram emptyEnv doc surf dropExpr of
    Left err ->
      assertBool "expected linear drop error" ("dropped" `T.isInfixOf` err && "linear" `T.isInfixOf` err)
    Right _ -> assertFailure "expected linear drop error"

testSurfaceModeEqComp :: Assertion
testSurfaceModeEqComp = do
  let src =
        T.unlines
          [ "doctrine SurfModes where {"
          , "  mode A;"
          , "  mode B;"
          , "  structure A = linear;"
          , "  structure B = linear;"
          , "  modality F : A -> B;"
          , "  modality U : B -> A;"
          , "  mod_eq U.F -> id@A;"
          , "  type Base @A;"
          , "  gen lift : [] -> [U(F(A.Base))] @A;"
          , "}"
          , "surface Seq where {"
          , "  doctrine SurfModes;"
          , "  mode A;"
          , "  lexer {"
          , "    keywords: lift, baseid;"
          , "    symbols: \";\";"
          , "  }"
          , "  expr {"
          , "    atom:"
          , "      \"lift\" => lift"
          , "    | \"baseid\" => id[Base]"
          , "    ;"
          , "    infixl 10 \";\" => $1 ; $2;"
          , "  }"
          , "}"
          ]
  env <- either (assertFailure . T.unpack) pure (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "SurfModes" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine SurfModes" >> fail "unreachable"
      Just d -> pure d
  surf <-
    case M.lookup "Seq" (meSurfaces env) of
      Nothing -> assertFailure "missing surface Seq" >> fail "unreachable"
      Just s -> pure s
  diag <- either (assertFailure . T.unpack) pure (elabSurfaceDiagram emptyEnv doc surf "lift ; baseid")
  dom <- either (assertFailure . T.unpack) pure (diagramDom diag)
  cod <- either (assertFailure . T.unpack) pure (diagramCod diag)
  let base = TCon (TypeRef (ModeName "A") (TypeName "Base")) []
  dom @?= []
  cod @?= [base]

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
  out <- either (assertFailure . T.unpack) pure (elabSurfaceDiagram env doc surf "use")
  iso <-
    case diagramIsoEq out termDiag of
      Left err -> assertFailure (T.unpack err)
      Right ok -> pure ok
  assertBool "expected spliced term diagram" iso

testSurfaceEliminatesToBaseDoctrine :: Assertion
testSurfaceEliminatesToBaseDoctrine = do
  let src =
        T.unlines
          [ "doctrine D where {"
          , "  mode M;"
          , "  structure M = linear;"
          , "  type A @M;"
          , "  gen f : [] -> [A] @M;"
          , "}"
          , "doctrine S extends D where {"
          , "  gen g : [] -> [A] @M;"
          , "  rule computational elim -> : [] -> [A] @M ="
          , "    g == f"
          , "}"
          , "surface Surf where {"
          , "  doctrine S;"
          , "  base D;"
          , "  mode M;"
          , "  lexer {"
          , "    keywords: g;"
          , "    symbols: ;"
          , "  }"
          , "  expr {"
          , "    atom: \"g\" => g;"
          , "  }"
          , "}"
          ]
  env <- either (assertFailure . T.unpack) pure (parseRawFile src >>= elabRawFile)
  docS <-
    case M.lookup "S" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine S" >> fail "unreachable"
      Just d -> pure d
  surf <-
    case M.lookup "Surf" (meSurfaces env) of
      Nothing -> assertFailure "missing surface Surf" >> fail "unreachable"
      Just s -> pure s
  (docOut, diagOut) <- either (assertFailure . T.unpack) pure (elabSurfaceExpr env docS surf "g")
  dName docOut @?= "D"
  let payloads = [ g | Edge _ (PGen g _ _) _ _ <- IM.elems (dEdges diagOut) ]
  assertBool "expected rewritten diagram to contain f" (GenName "f" `elem` payloads)
  assertBool "expected rewritten diagram to eliminate g" (GenName "g" `notElem` payloads)
