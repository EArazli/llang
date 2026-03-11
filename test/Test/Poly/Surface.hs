{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
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
import Strat.Poly.ModeTheory (ModeName(..), ClassificationDecl(..), ModeTheory(..))
import Strat.Poly.Obj (Obj(..), ObjName(..), ObjRef(..), CodeArg(..), CodeTerm(..), mkCon, mkModeMetaVar, boundTmIndicesTerm)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), GenParam(..), InputShape(..), genericGenDiagram)
import Strat.Poly.Morphism (Morphism(..), MorphismCheck(..), GenImage(..))
import Strat.Poly.Surface.Parse (parseSurfaceSpec)
import Strat.Poly.Surface (PolySurfaceDef, elabPolySurfaceDecl)
import Strat.Poly.Surface.Elab (elabSurfaceExpr)
import Strat.Poly.Diagram (idD, genD, diagramDom, diagramCod)
import Strat.Poly.Graph (Diagram(..), Edge(..), EdgePayload(..), unPortId)
import Strat.Poly.DiagramIso (diagramIsoEq)
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
    , testCase "surface resolves classified constructors in classifier mode with owner preserved" testSurfaceClassifiedTypeResolution
    , testCase "surface bare identifiers prefer nullary constructors over metas" testSurfaceBareIdentResolvesNullaryConstructor
    , testCase "surface elaborates constructor args in signature owner modes" testSurfaceConstructorArgOwnerModes
    , testCase "surface type annotations support term-indexed constructor args" testSurfaceConstructorTermArgInTypeAnnotation
    , testCase "surface term-indexed annotations can reference bound terms" testSurfaceConstructorTermArgUsesBoundBinder
    , testCase "template @TermName splice uses module term" testSurfaceTemplateSplice
    , testCase "surface template trace elaborates to feedback with outer boundary" testSurfaceTemplateTrace
    , testCase "surface elaboration eliminates to base doctrine" testSurfaceEliminatesToBaseDoctrine
    ]


specText :: Text
specText =
  T.unlines
    [ "doctrine TestDoc;"
    , "  mode M;"
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
    , "  mode M;"
    , "lexer {"
    , "  keywords: use;"
    , "  symbols: ;"
    , "}"
    , "expr {"
    , "  atom: \"use\" => @T;"
    , "}"
    ]

traceTemplateSpecText :: Text
traceTemplateSpecText =
  T.unlines
    [ "doctrine TestDoc;"
    , "  mode M;"
    , "lexer {"
    , "  symbols: ;"
    , "}"
    , "expr {"
    , "  atom:"
    , "    ident(name) => trace 1 { #name };"
    , "}"
    ]

modeM :: ModeName
modeM = ModeName "M"

typeA :: Obj
typeA = mkCon (ObjRef modeM (ObjName "A")) []

mkDoctrine :: Bool -> Bool -> Doctrine
mkDoctrine hasDup hasDrop =
  let uRef = ObjRef modeM (ObjName "U_M")
      universe = mkCon uRef []
      classifiedModes =
        (mkModes [modeM])
          { mtClassifiedBy =
              M.singleton
                modeM
                ClassificationDecl
                  { cdClassifier = modeM
                  , cdUniverse = universe
                  
                  , cdComp = Nothing
                  }
          }
      aVar = mkModeMetaVar "a" modeM
      mkGen name tyVars dom cod =
        GenDecl
          { gdName = GenName name
          , gdMode = modeM
          , gdParams = map GP_Ty tyVars
          , gdDom = map InPort dom
          , gdCod = cod
          , gdLiteralKind = Nothing
          }
      genDup = mkGen "dup" [aVar] [OVar aVar] [OVar aVar, OVar aVar]
      genDrop = mkGen "drop" [aVar] [OVar aVar] []
      genA = mkGen "A" [] [] [universe]
      genF = mkGen "f" [] [typeA, typeA] [typeA]
      genStep2 = mkGen "step2" [] [typeA, typeA] [typeA, typeA]
      genUnit = mkGen "unit" [] [] [typeA]
      gens =
        [ (GenName "A", genA)
        , (GenName "f", genF)
        , (GenName "step2", genStep2)
        , (GenName "unit", genUnit)
        ]
          <> [ (GenName "dup", genDup) | hasDup ]
          <> [ (GenName "drop", genDrop) | hasDrop ]
   in Doctrine
        { dName = "TestDoc"
        , dModes = classifiedModes
        , dAcyclicModes = S.empty
        , dGens = M.fromList [(modeM, M.fromList gens)]
        , dCells2 = []
        , dActions = M.empty
        , dObligations = []
                }

mkSurfaceWithSpec :: Text -> Doctrine -> Either Text PolySurfaceDef
mkSurfaceWithSpec txt doc = do
  spec <- parseSurfaceSpec txt
  elabPolySurfaceDecl "TestSurface" doc Nothing spec

mkStructEnv :: Doctrine -> Either Text ModuleEnv
mkStructEnv target = do
  let uRef = ObjRef modeM (ObjName "U_M")
      universe = mkCon uRef []
      classifiedModes =
        (mkModes [modeM])
          { mtClassifiedBy =
              M.singleton
                modeM
                ClassificationDecl
                  { cdClassifier = modeM
                  , cdUniverse = universe
                  
                  , cdComp = Nothing
                  }
          }
      aVar = mkModeMetaVar "a" modeM
      mkGen name cod =
        GenDecl
          { gdName = GenName name
          , gdMode = modeM
          , gdParams = [GP_Ty (aVar)]
          , gdDom = [InPort (OVar aVar)]
          , gdCod = cod
          , gdLiteralKind = Nothing
          }
      iface =
        Doctrine
          { dName = "StructCartesian"
          , dModes = classifiedModes
          , dAcyclicModes = S.empty
          , dGens =
              M.fromList
                [ ( modeM
                  , M.fromList
                      [ (GenName "dup", mkGen "dup" [OVar aVar, OVar aVar])
                      , (GenName "drop", mkGen "drop" [])
                      ]
                  )
                ]
          , dCells2 = []
          , dActions = M.empty
          , dObligations = []
                    }
  dupImg <- genericGenDiagram (mkGen "dup" [OVar aVar, OVar aVar])
  dropImg <- genericGenDiagram (mkGen "drop" [])
  let morph =
        Morphism
          { morName = "Test.structInst"
          , morSrc = iface
          , morTgt = target
          , morIsCoercion = False
          , morModeMap = M.singleton modeM modeM
          , morModMap = M.empty
          , morTypeMap = M.empty
          , morGenMap =
              M.fromList
                [ ((modeM, GenName "dup"), GenImage dupImg M.empty)
                , ((modeM, GenName "drop"), GenImage dropImg M.empty)
                ]
          , morCheck = CheckNone
          , morPolicy = UseAllOriented
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
  diag <- either (assertFailure . T.unpack) pure (elabSurfaceDiagram emptyEnv doc surf expr)
  inPort <-
    case dIn diag of
      [p] -> pure p
      _ -> assertFailure "expected one input port" >> fail "unreachable"
  inTy <-
    case IM.lookup (unPortId inPort) (dPortObj diag) of
      Nothing -> assertFailure "missing input port object" >> fail "unreachable"
      Just ty -> pure ty
  case objCode inTy of
    CTCon ref [] -> ref @?= ObjRef modeM (ObjName "A")
    _ -> assertFailure "expected bare A to resolve as nullary constructor code"

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
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen dup (a@M) : [a] -> [a, a] @M;"
          , "  gen drop (a@M) : [a] -> [] @M;"
          , "}"
          , "doctrine Target where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen A : [] -> [M.U_M] @M;"
          , "  gen copy (a@M) : [a] -> [a, a] @M;"
          , "  gen kill (a@M) : [a] -> [] @M;"
          , "  gen f : [A, A] -> [A] @M;"
          , "  gen unit : [] -> [A] @M;"
          , "}"
          , "morphism cartInst : StructCartesian -> Target where {"
          , "  mode M -> M;"
          , "  gen comp_ctx_ext @M -> comp_ctx_ext(a)"
          , "  gen comp_var @M -> comp_var(a)"
          , "  gen comp_reindex @M -> comp_reindex(a)"
          , "  gen dup @M -> copy(a)"
          , "  gen drop @M -> kill(a)"
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
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen dup (a@M) : [a] -> [a, a] @M;"
          , "  gen drop (a@M) : [a] -> [] @M;"
          , "}"
          , "doctrine Target where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen A : [] -> [M.U_M] @M;"
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
          , "  mode A classifiedBy A via A.U_A;"
          , "  gen comp_ctx_ext(a@A) : [a] -> [a] @A;"
          , "  gen comp_var(a@A) : [a] -> [a] @A;"
          , "  gen comp_reindex(a@A) : [a] -> [a] @A;"
          , "  comprehension A where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_A : [] -> [A.U_A] @A;"
          , "  mode B classifiedBy A via A.U_A;"
          , "  gen comp_ctx_ext(a@B) : [a] -> [a] @B;"
          , "  gen comp_var(a@B) : [a] -> [a] @B;"
          , "  gen comp_reindex(a@B) : [a] -> [a] @B;"
          , "  comprehension B where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  modality F : A -> B;"
          , "  modality U : B -> A;"
          , "  lift_classifier F = id@A;"
          , "  lift_classifier U = id@A;"
          , "  mod_eq U.F -> id@A;"
          , "  gen Base : [] -> [A.U_A] @A;"
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
  let base = mkCon (ObjRef (ModeName "A") (ObjName "Base")) []
  dom @?= []
  cod @?= [base]

testSurfaceClassifiedTypeResolution :: Assertion
testSurfaceClassifiedTypeResolution = do
  let src =
        T.unlines
          [ "doctrine SurfClassified where {"
          , "  mode Ty classifiedBy Ty via Ty.U_Ty;"
          , "  gen comp_ctx_ext(a@Ty) : [a] -> [a] @Ty;"
          , "  gen comp_var(a@Ty) : [a] -> [a] @Ty;"
          , "  gen comp_reindex(a@Ty) : [a] -> [a] @Ty;"
          , "  comprehension Ty where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_Ty : [] -> [Ty.U_Ty] @Ty;"
          , "  mode Tm classifiedBy Ty via Ty.U;"
          , "  gen comp_ctx_ext(a@Tm) : [a] -> [a] @Tm;"
          , "  gen comp_var(a@Tm) : [a] -> [a] @Tm;"
          , "  gen comp_reindex(a@Tm) : [a] -> [a] @Tm;"
          , "  comprehension Tm where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U : [] -> [Ty.U_Ty] @Ty;"
          , "  gen Unit : [] -> [Ty.U] @Ty;"
          , "  gen Arr(a@Tm, b@Tm) : [] -> [Ty.U] @Ty;"
          , "}"
          , "surface Surf where {"
          , "  doctrine SurfClassified;"
          , "  mode Tm;"
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
    case M.lookup "SurfClassified" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine SurfClassified" >> fail "unreachable"
      Just d -> pure d
  surf <-
    case M.lookup "Surf" (meSurfaces env) of
      Nothing -> assertFailure "missing surface Surf" >> fail "unreachable"
      Just s -> pure s
  diag <-
    either
      (assertFailure . T.unpack)
      pure
      (elabSurfaceDiagram emptyEnv doc surf (T.unlines [ "term {", "  in x:Unit;", "  out x", "}" ]))
  inPort <-
    case dIn diag of
      [p] -> pure p
      _ -> assertFailure "expected one input port" >> fail "unreachable"
  outPort <-
    case dOut diag of
      [p] -> pure p
      _ -> assertFailure "expected one output port" >> fail "unreachable"
  inTy <-
    case IM.lookup (unPortId inPort) (dPortObj diag) of
      Nothing -> assertFailure "missing input port object" >> fail "unreachable"
      Just ty -> pure ty
  outTy <-
    case IM.lookup (unPortId outPort) (dPortObj diag) of
      Nothing -> assertFailure "missing output port object" >> fail "unreachable"
      Just ty -> pure ty
  assertUnit inTy
  outTy @?= inTy
  where
    tmMode = ModeName "Tm"
    tyMode = ModeName "Ty"
    unitRef = ObjRef tyMode (ObjName "Unit")

    assertUnit ty = do
      objOwnerMode ty @?= tmMode
      case objCode ty of
        CTCon ref [] -> ref @?= unitRef
        _ -> assertFailure "expected Unit code"

testSurfaceBareIdentResolvesNullaryConstructor :: Assertion
testSurfaceBareIdentResolvesNullaryConstructor = do
  let doc = mkDoctrine True True
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec specText doc)
  diag <-
    either
      (assertFailure . T.unpack)
      pure
      (elabSurfaceDiagram emptyEnv doc surf (T.unlines [ "term {", "  in x:A;", "  out x", "}" ]))
  inPort <-
    case dIn diag of
      [p] -> pure p
      _ -> assertFailure "expected one input port" >> fail "unreachable"
  inTy <-
    case IM.lookup (unPortId inPort) (dPortObj diag) of
      Nothing -> assertFailure "missing input port object" >> fail "unreachable"
      Just ty -> pure ty
  case objCode inTy of
    CTCon ref [] -> ref @?= ObjRef modeM (ObjName "A")
    _ -> assertFailure "expected bare A to resolve as nullary constructor code"

testSurfaceConstructorArgOwnerModes :: Assertion
testSurfaceConstructorArgOwnerModes = do
  let src =
        T.unlines
          [ "doctrine SurfCrossMode where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  mode N classifiedBy N via N.U_N;"
          , "  gen comp_ctx_ext(a@N) : [a] -> [a] @N;"
          , "  gen comp_var(a@N) : [a] -> [a] @N;"
          , "  gen comp_reindex(a@N) : [a] -> [a] @N;"
          , "  comprehension N where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_N : [] -> [N.U_N] @N;"
          , "  gen B : [] -> [N.U_N] @N;"
          , "  gen WrapN(x@N) : [] -> [M.U_M] @M;"
          , "}"
          , "surface Surf where {"
          , "  doctrine SurfCrossMode;"
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
    case M.lookup "SurfCrossMode" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine SurfCrossMode" >> fail "unreachable"
      Just d -> pure d
  surf <-
    case M.lookup "Surf" (meSurfaces env) of
      Nothing -> assertFailure "missing surface Surf" >> fail "unreachable"
      Just s -> pure s
  diag <-
    either
      (assertFailure . T.unpack)
      pure
      (elabSurfaceDiagram emptyEnv doc surf (T.unlines [ "term {", "  in x:WrapN(B);", "  out x", "}" ]))
  inPort <-
    case dIn diag of
      [p] -> pure p
      _ -> assertFailure "expected one input port" >> fail "unreachable"
  inTy <-
    case IM.lookup (unPortId inPort) (dPortObj diag) of
      Nothing -> assertFailure "missing input port object" >> fail "unreachable"
      Just ty -> pure ty
  let mMode = ModeName "M"
  let nMode = ModeName "N"
  objOwnerMode inTy @?= mMode
  case objCode inTy of
    CTCon wrapRef [CAObj argTy] -> do
      wrapRef @?= ObjRef mMode (ObjName "WrapN")
      objOwnerMode argTy @?= nMode
      case objCode argTy of
        CTCon bRef [] -> bRef @?= ObjRef nMode (ObjName "B")
        _ -> assertFailure "expected WrapN argument to elaborate as N.B constructor"
    _ -> assertFailure "expected WrapN(B) object code"

testSurfaceConstructorTermArgInTypeAnnotation :: Assertion
testSurfaceConstructorTermArgInTypeAnnotation = do
  let src =
        T.unlines
          [ "doctrine SurfTermIndexed where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen Nat : [] -> [M.U_M] @M;"
          , "  gen Z : [] -> [Nat] @M;"
          , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
          , "}"
          , "surface Surf where {"
          , "  doctrine SurfTermIndexed;"
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
    case M.lookup "SurfTermIndexed" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine SurfTermIndexed" >> fail "unreachable"
      Just d -> pure d
  surf <-
    case M.lookup "Surf" (meSurfaces env) of
      Nothing -> assertFailure "missing surface Surf" >> fail "unreachable"
      Just s -> pure s
  diag <-
    either
      (assertFailure . T.unpack)
      pure
      (elabSurfaceDiagram emptyEnv doc surf (T.unlines [ "term {", "  in x:Vec(Z);", "  out x", "}" ]))
  inPort <-
    case dIn diag of
      [p] -> pure p
      _ -> assertFailure "expected one input port" >> fail "unreachable"
  inTy <-
    case IM.lookup (unPortId inPort) (dPortObj diag) of
      Nothing -> assertFailure "missing input port object" >> fail "unreachable"
      Just ty -> pure ty
  case objCode inTy of
    CTCon ref [CATm _] -> ref @?= ObjRef (ModeName "M") (ObjName "Vec")
    _ -> assertFailure "expected Vec(Z) to elaborate with a CATm term argument"

testSurfaceConstructorTermArgUsesBoundBinder :: Assertion
testSurfaceConstructorTermArgUsesBoundBinder = do
  let src =
        T.unlines
          [ "doctrine SurfTermIndexed where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen Nat : [] -> [M.U_M] @M;"
          , "  gen Z : [] -> [Nat] @M;"
          , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
          , "}"
          , "surface Surf where {"
          , "  doctrine SurfTermIndexed;"
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
    case M.lookup "SurfTermIndexed" (meDoctrines env) of
      Nothing -> assertFailure "missing doctrine SurfTermIndexed" >> fail "unreachable"
      Just d -> pure d
  surf <-
    case M.lookup "Surf" (meSurfaces env) of
      Nothing -> assertFailure "missing surface Surf" >> fail "unreachable"
      Just s -> pure s
  diag <-
    either
      (assertFailure . T.unpack)
      pure
      (elabSurfaceDiagram emptyEnv doc surf (T.unlines [ "term {", "  in n:Nat;", "  in x:Vec(n);", "  out n, x", "}" ]))
  inPorts <-
    case dIn diag of
      [p0, p1] -> pure (p0, p1)
      _ -> assertFailure "expected two input ports" >> fail "unreachable"
  xTy <-
    case IM.lookup (unPortId (snd inPorts)) (dPortObj diag) of
      Nothing -> assertFailure "missing x input port object" >> fail "unreachable"
      Just ty -> pure ty
  case objCode xTy of
    CTCon ref [CATm tm] -> do
      ref @?= ObjRef (ModeName "M") (ObjName "Vec")
      assertBool "expected Vec(n) term arg to reference an in-scope bound term" (not (S.null (boundTmIndicesTerm tm)))
    _ -> assertFailure "expected Vec(n) to elaborate with a CATm bound-term argument"

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

testSurfaceTemplateTrace :: Assertion
testSurfaceTemplateTrace = do
  let doc = mkDoctrine True True
  surf <- either (assertFailure . T.unpack) pure (mkSurfaceWithSpec traceTemplateSpecText doc)
  diag <- either (assertFailure . T.unpack) pure (elabSurfaceDiagram emptyEnv doc surf "step2")
  assertEqual "trace should expose one outer input" 1 (length (dIn diag))
  assertEqual "trace should expose one outer output" 1 (length (dOut diag))
  case IM.elems (dEdges diag) of
    [Edge _ (PFeedback body) ins outs] -> do
      assertEqual "feedback edge should consume one outer input" 1 (length ins)
      assertEqual "feedback edge should produce one outer output" 1 (length outs)
      assertEqual "feedback body should have two inputs" 2 (length (dIn body))
      assertEqual "feedback body should have two outputs" 2 (length (dOut body))
    _ -> assertFailure "expected exactly one feedback edge"

testSurfaceEliminatesToBaseDoctrine :: Assertion
testSurfaceEliminatesToBaseDoctrine = do
  let src =
        T.unlines
          [ "doctrine D where {"
          , "  mode M classifiedBy M via M.U_M;"
          , "  gen comp_ctx_ext(a@M) : [a] -> [a] @M;"
          , "  gen comp_var(a@M) : [a] -> [a] @M;"
          , "  gen comp_reindex(a@M) : [a] -> [a] @M;"
          , "  comprehension M where { ctx_ext = comp_ctx_ext; var = comp_var; reindex = comp_reindex; };"
          , "  gen U_M : [] -> [M.U_M] @M;"
          , "  gen A : [] -> [M.U_M] @M;"
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
