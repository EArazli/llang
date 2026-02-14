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
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..), TyVar(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..), InputShape(..))
import Strat.Poly.Morphism (Morphism(..), MorphismCheck(..), GenImage(..))
import Strat.Poly.Surface.Parse (parseSurfaceSpec)
import Strat.Poly.Surface (PolySurfaceDef, elabPolySurfaceDecl)
import Strat.Poly.Surface.Elab (elabSurfaceExpr)
import Strat.Poly.Diagram (idD, genD, diagramDom, diagramCod)
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
    , testCase "surface resolves dup/drop through implements StructCartesian" testSurfaceStructImplements
    , testCase "surface rejects dup/drop without StructCartesian instance" testSurfaceStructMissing
    , testCase "surface rejects duplication without dup capability" testSurfaceRejectsDupWithoutCapability
    , testCase "surface rejects drop without drop capability" testSurfaceRejectsDropWithoutCapability
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

mkDoctrine :: Bool -> Bool -> Doctrine
mkDoctrine hasDup hasDrop =
  let aVar = TyVar { tvName = "a", tvMode = modeM }
      mkGen name tyVars dom cod =
        GenDecl
          { gdName = GenName name
          , gdMode = modeM
          , gdTyVars = tyVars
          , gdTmVars = []
          , gdDom = map InPort dom
          , gdCod = cod
          , gdAttrs = []
          }
      genDup = mkGen "dup" [aVar] [TVar aVar] [TVar aVar, TVar aVar]
      genDrop = mkGen "drop" [aVar] [TVar aVar] []
      genF = mkGen "f" [] [typeA, typeA] [typeA]
      genUnit = mkGen "unit" [] [] [typeA]
      gens =
        [ (GenName "f", genF)
        , (GenName "unit", genUnit)
        ]
          <> [ (GenName "dup", genDup) | hasDup ]
          <> [ (GenName "drop", genDrop) | hasDrop ]
   in Doctrine
        { dName = "TestDoc"
        , dModes = mkModes [modeM]
        , dAcyclicModes = S.empty
        , dTypes = M.fromList [(modeM, M.fromList [(TypeName "A", TypeSig [])])]
        , dGens = M.fromList [(modeM, M.fromList gens)]
        , dCells2 = []
      , dActions = M.empty
      , dObligations = []
        , dAttrSorts = M.empty
        }

mkSurfaceWithSpec :: Text -> Doctrine -> Either Text PolySurfaceDef
mkSurfaceWithSpec txt doc = do
  spec <- parseSurfaceSpec txt
  elabPolySurfaceDecl "TestSurface" doc Nothing spec

mkStructEnv :: Doctrine -> Either Text ModuleEnv
mkStructEnv target = do
  let aVar = TyVar { tvName = "a", tvMode = modeM }
      mkGen name cod =
        GenDecl
          { gdName = GenName name
          , gdMode = modeM
          , gdTyVars = [aVar]
          , gdTmVars = []
          , gdDom = [InPort (TVar aVar)]
          , gdCod = cod
          , gdAttrs = []
          }
      iface =
        Doctrine
          { dName = "StructCartesian"
          , dModes = mkModes [modeM]
          , dAcyclicModes = S.empty
          , dTypes = M.empty
          , dGens =
              M.fromList
                [ ( modeM
                  , M.fromList
                      [ (GenName "dup", mkGen "dup" [TVar aVar, TVar aVar])
                      , (GenName "drop", mkGen "drop" [])
                      ]
                  )
                ]
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
          , dAttrSorts = M.empty
          }
  dupImg <- genD modeM [TVar aVar] [TVar aVar, TVar aVar] (GenName "dup")
  dropImg <- genD modeM [TVar aVar] [] (GenName "drop")
  let morph =
        Morphism
          { morName = "Test.structInst"
          , morSrc = iface
          , morTgt = target
          , morIsCoercion = False
          , morModeMap = M.singleton modeM modeM
          , morModMap = M.empty
          , morAttrSortMap = M.empty
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                [ ((modeM, GenName "dup"), GenImage dupImg M.empty)
                , ((modeM, GenName "drop"), GenImage dropImg M.empty)
                ]
          , morCheck = CheckNone
          , morPolicy = UseAllOriented
          , morFuel = 20
          }
  pure
    emptyEnv
      { meDoctrines =
          M.fromList
            [ (dName target, target)
            , ("StructCartesian", iface)
            ]
      , meMorphisms = M.singleton "Test.structInst" morph
      , meImplDefaults = M.singleton ("StructCartesian", dName target) ["Test.structInst"]
      }

elabSurfaceDiagram :: ModuleEnv -> Doctrine -> PolySurfaceDef -> Text -> Either Text Diagram
elabSurfaceDiagram env doc surf expr =
  fmap snd (elabSurfaceExpr env doc surf expr)

assertHasGen :: Text -> Diagram -> Assertion
assertHasGen name diag =
  let payloads = [ g | Edge _ (PGen g _ _) _ _ <- IM.elems (dEdges diag) ]
   in if GenName name `elem` payloads then pure () else assertFailure ("expected gen " <> T.unpack name)

testSurfaceElabOk :: Assertion
testSurfaceElabOk = do
  let doc = mkDoctrine True True
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out x", "}" ]
  case elabSurfaceDiagram emptyEnv doc surf expr of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testSurfaceDup :: Assertion
testSurfaceDup = do
  let doc = mkDoctrine True True
  env <- either (assertFailure . T.unpack) pure (mkStructEnv doc)
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out f(x, x)", "}" ]
  case elabSurfaceDiagram env doc surf expr of
    Left err -> assertFailure (T.unpack err)
    Right diag -> assertHasGen "dup" diag

testSurfaceDupLeftAssociated :: Assertion
testSurfaceDupLeftAssociated = do
  let doc = mkDoctrine True True
  env <- either (assertFailure . T.unpack) pure (mkStructEnv doc)
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out x, x, x", "}" ]
  diag <- either (assertFailure . T.unpack) pure (elabSurfaceDiagram env doc surf expr)
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
  let doc = mkDoctrine True True
  env <- either (assertFailure . T.unpack) pure (mkStructEnv doc)
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out unit", "}" ]
  case elabSurfaceDiagram env doc surf expr of
    Left err -> assertFailure (T.unpack err)
    Right diag -> assertHasGen "drop" diag

testSurfaceStructImplements :: Assertion
testSurfaceStructImplements = do
  let src =
        T.unlines
          [ "doctrine StructCartesian where {"
          , "  mode M;"
          , "  gen dup (a@M) : [a] -> [a, a] @M;"
          , "  gen drop (a@M) : [a] -> [] @M;"
          , "}"
          , "doctrine Target where {"
          , "  mode M;"
          , "  type A @M;"
          , "  gen copy (a@M) : [a] -> [a, a] @M;"
          , "  gen kill (a@M) : [a] -> [] @M;"
          , "  gen f : [A, A] -> [A] @M;"
          , "  gen unit : [] -> [A] @M;"
          , "}"
          , "morphism cartInst : StructCartesian -> Target where {"
          , "  mode M -> M;"
          , "  gen dup @M -> copy"
          , "  gen drop @M -> kill"
          , "  check none;"
          , "}"
          , "implements StructCartesian for Target using cartInst;"
          , "surface Surf where {"
          , "  doctrine Target;"
          , "  mode M;"
          , "  lexer {"
          , "    keywords: term, in, out;"
          , "    symbols: \"(\", \")\", \"{\", \"}\", \":\", \";\", \",\";"
          , "  }"
          , "  expr {"
          , "    atom:"
          , "      ident(name) \"(\" <expr> \")\" => $1 ; #name"
          , "    | ident(name) => $name"
          , "    | \"out\" <expr> => $1"
          , "    | \"term\" \"{\" <expr> \"}\" => $1"
          , "    | \"(\" <expr> \")\" => <expr>"
          , "    ;"
          , "    prefix:"
          , "      \"in\" ident(name) \":\" <type>(ty) \";\" <expr> => <expr> bind in(name, ty, 1)"
          , "    ;"
          , "    infixr 10 \",\" => $1 * $2;"
          , "  }"
          , "}"
          ]
  env <- either (assertFailure . T.unpack) pure (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "Target" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine Target" >> fail "unreachable"
      Just d -> pure d
  surf <-
    case M.lookup "Surf" (meSurfaces env) of
      Nothing -> assertFailure "missing surface Surf" >> fail "unreachable"
      Just s -> pure s
  diagDup <-
    either
      (assertFailure . T.unpack)
      pure
      (elabSurfaceDiagram env doc surf (T.unlines [ "term {", "  in x:A;", "  out f(x, x)", "}" ]))
  assertHasGen "copy" diagDup
  diagDrop <-
    either
      (assertFailure . T.unpack)
      pure
      (elabSurfaceDiagram env doc surf (T.unlines [ "term {", "  in x:A;", "  out unit", "}" ]))
  assertHasGen "kill" diagDrop

testSurfaceStructMissing :: Assertion
testSurfaceStructMissing = do
  let src =
        T.unlines
          [ "doctrine StructCartesian where {"
          , "  mode M;"
          , "  gen dup (a@M) : [a] -> [a, a] @M;"
          , "  gen drop (a@M) : [a] -> [] @M;"
          , "}"
          , "doctrine Target where {"
          , "  mode M;"
          , "  type A @M;"
          , "  gen copy (a@M) : [a] -> [a, a] @M;"
          , "  gen kill (a@M) : [a] -> [] @M;"
          , "  gen f : [A, A] -> [A] @M;"
          , "  gen unit : [] -> [A] @M;"
          , "}"
          , "surface Surf where {"
          , "  doctrine Target;"
          , "  mode M;"
          , "  lexer {"
          , "    keywords: term, in, out;"
          , "    symbols: \"(\", \")\", \"{\", \"}\", \":\", \";\", \",\";"
          , "  }"
          , "  expr {"
          , "    atom:"
          , "      ident(name) \"(\" <expr> \")\" => $1 ; #name"
          , "    | ident(name) => $name"
          , "    | \"out\" <expr> => $1"
          , "    | \"term\" \"{\" <expr> \"}\" => $1"
          , "    | \"(\" <expr> \")\" => <expr>"
          , "    ;"
          , "    prefix:"
          , "      \"in\" ident(name) \":\" <type>(ty) \";\" <expr> => <expr> bind in(name, ty, 1)"
          , "    ;"
          , "    infixr 10 \",\" => $1 * $2;"
          , "  }"
          , "}"
          ]
  env <- either (assertFailure . T.unpack) pure (parseRawFile src >>= elabRawFile)
  doc <-
    case M.lookup "Target" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine Target" >> fail "unreachable"
      Just d -> pure d
  surf <-
    case M.lookup "Surf" (meSurfaces env) of
      Nothing -> assertFailure "missing surface Surf" >> fail "unreachable"
      Just s -> pure s
  case elabSurfaceDiagram env doc surf (T.unlines [ "term {", "  in x:A;", "  out f(x, x)", "}" ]) of
    Left err -> assertBool "expected missing dup capability error" ("no dup capability" `T.isInfixOf` err)
    Right _ -> assertFailure "expected duplication capability error"
  case elabSurfaceDiagram env doc surf (T.unlines [ "term {", "  in x:A;", "  out unit", "}" ]) of
    Left err -> assertBool "expected missing drop capability error" ("no drop capability" `T.isInfixOf` err)
    Right _ -> assertFailure "expected drop capability error"

testSurfaceRejectsDupWithoutCapability :: Assertion
testSurfaceRejectsDupWithoutCapability = do
  let doc = mkDoctrine False True
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out f(x, x)", "}" ]
  case elabSurfaceDiagram emptyEnv doc surf expr of
    Left err ->
      assertBool "expected duplication capability error" ("no dup capability" `T.isInfixOf` err)
    Right _ -> assertFailure "expected duplication capability error"

testSurfaceRejectsDropWithoutCapability :: Assertion
testSurfaceRejectsDropWithoutCapability = do
  let doc = mkDoctrine True False
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  let expr = T.unlines [ "term {", "  in x:A;", "  out unit", "}" ]
  case elabSurfaceDiagram emptyEnv doc surf expr of
    Left err ->
      assertBool "expected drop capability error" ("no drop capability" `T.isInfixOf` err)
    Right _ -> assertFailure "expected drop capability error"

testSurfaceModeEqComp :: Assertion
testSurfaceModeEqComp = do
  let src =
        T.unlines
          [ "doctrine SurfModes where {"
          , "  mode A;"
          , "  mode B;"
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
  let doc = mkDoctrine True True
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
