{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.ClassificationResolution
  ( tests
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Strat.DSL.Elab (elabRawFile)
import Strat.DSL.Parse (parseRawFile)
import Strat.Frontend.Env (ModuleEnv, meDoctrines)
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , GenDecl(..)
  , doctrineTypeTheory
  , gdPlainDom
  , lookupCtorSigForOwner
  )
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
  ( CodeArg(..)
  , CodeTerm(..)
  , Obj(..)
  , ObjName(..)
  , ObjRef(..)
  , TmFunName(..)
  )
import Strat.Poly.DefEq (diagramToTermExprChecked, normalizeObjDeepWithCtx)
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.TypeTheory (TypeParamSig(..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit


tests :: TestTree
tests =
  testGroup
    "Poly.ClassificationResolution"
    [ testCase "classifier mode drives constructor resolution" testClassifierResolution
    , testCase "wrong constructor qualifier is rejected for classified objects" testWrongClassifierQualifier
    , testCase "normalizeObjDeep preserves and normalizes term arguments under Obj wrapper" testTermArgNormalization
    ]


testClassifierResolution :: Assertion
testClassifierResolution = do
  let src = T.unlines
        [ "doctrine ClassifyResolve where {"
        , "  mode Ty classifiedBy Ty via Ty.U;"
        , "  mode Tm classifiedBy Ty via Ty.U;"
        , "  gen U : [] -> [Ty.U] @Ty;"
        , "  gen Unit : [] -> [Ty.U] @Ty;"
        , "  gen Arr(a@Tm, b@Tm) : [] -> [Ty.U] @Ty;"
        , "  gen idArr : [Arr(Unit, Unit)] -> [Arr(Unit, Unit)] @Tm;"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <- lookupDoctrine env "ClassifyResolve"
  gen <- lookupGenDecl doc (ModeName "Tm") (GenName "idArr")
  case gdPlainDom gen of
    [arrObj] -> do
      objOwnerMode arrObj @?= ModeName "Tm"
      case objCode arrObj of
        CTCon ref [CAObj aObj, CAObj bObj] -> do
          ref @?= ObjRef (ModeName "Ty") (ObjName "Arr")
          assertUnitObj aObj
          assertUnitObj bObj
        _ ->
          assertFailure "expected Arr(Unit, Unit) code in Ty classifier"
    _ ->
      assertFailure "expected idArr to have exactly one input"
  where
    assertUnitObj obj = do
      objOwnerMode obj @?= ModeName "Tm"
      case objCode obj of
        CTCon ref [] ->
          ref @?= ObjRef (ModeName "Ty") (ObjName "Unit")
        _ ->
          assertFailure "expected Unit classifier code"


testWrongClassifierQualifier :: Assertion
testWrongClassifierQualifier = do
  let src = T.unlines
        [ "doctrine WrongQualifier where {"
        , "  mode Ty classifiedBy Ty via Ty.U;"
        , "  mode Tm classifiedBy Ty via Ty.U;"
        , "  gen U : [] -> [Ty.U] @Ty;"
        , "  gen Unit : [] -> [Ty.U] @Ty;"
        , "  gen Arr(a@Tm, b@Tm) : [] -> [Ty.U] @Ty;"
        , "  gen bad : [Tm.Arr(Unit, Unit)] -> [Tm.Arr(Unit, Unit)] @Tm;"
        , "}"
        ]
  case parseRawFile src >>= elabRawFile of
    Left err -> do
      assertBool "expected classifier mode in error" ("classified by Ty" `T.isInfixOf` err)
      assertBool "expected qualifier mismatch in error" ("qualifier Tm" `T.isInfixOf` err)
    Right _ ->
      assertFailure "expected elaboration failure for wrong constructor qualifier"


testTermArgNormalization :: Assertion
testTermArgNormalization = do
  let src = T.unlines
        [ "doctrine ClassifyNormalize where {"
        , "  mode Ty classifiedBy Ty via Ty.U;"
        , "  mode Tm classifiedBy Ty via Ty.U;"
        , "  gen U : [] -> [Ty.U] @Ty;"
        , "  gen Nat : [] -> [Ty.U] @Ty;"
        , "  gen Unit : [] -> [Ty.U] @Ty;"
        , "  gen Z : [] -> [Nat] @Ty;"
        , "  gen S : [Nat] -> [Nat] @Ty;"
        , "  gen Vec(n : Nat, a@Tm) : [] -> [Ty.U] @Ty;"
        , "  gen mk : [] -> [Vec(S(Z), Unit)] @Tm;"
        , "}"
        ]
  env <- requireEither (parseRawFile src >>= elabRawFile)
  doc <- lookupDoctrine env "ClassifyNormalize"
  tt <- requireEither (doctrineTypeTheory doc)
  gen <- lookupGenDecl doc (ModeName "Tm") (GenName "mk")
  vecSort <-
    case gdCod gen of
      [obj] -> pure obj
      _ -> assertFailure "expected mk to have exactly one output" >> fail "unreachable"
  vecNorm <- requireEither (normalizeObjDeepWithCtx tt [] vecSort)
  objOwnerMode vecNorm @?= ModeName "Tm"
  case objCode vecNorm of
    CTCon ref [CATm nTm, CAObj aObj] -> do
      ref @?= ObjRef (ModeName "Ty") (ObjName "Vec")
      objOwnerMode aObj @?= ModeName "Tm"
      case objCode aObj of
        CTCon unitRef [] ->
          unitRef @?= ObjRef (ModeName "Ty") (ObjName "Unit")
        _ ->
          assertFailure "expected Unit classifier code in Vec second argument"
      natSort <- lookupNatSort doc ref
      nExpr <- requireEither (diagramToTermExprChecked tt [] natSort nTm)
      nExpr @?= TMFun (TmFunName "S") [TMFun (TmFunName "Z") []]
    _ ->
      assertFailure "expected Vec(term, obj) code shape"
  where
    lookupNatSort doc vecRef = do
      params <- requireEither (lookupCtorSigForOwner doc (ModeName "Tm") vecRef)
      case params of
        (TPS_Tm natSort : _) -> pure natSort
        _ -> assertFailure "expected Vec to have first term parameter" >> fail "unreachable"


lookupDoctrine :: ModuleEnv -> T.Text -> IO Doctrine
lookupDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> assertFailure ("missing doctrine: " <> T.unpack name) >> fail "unreachable"
    Just doc -> pure doc


lookupGenDecl :: Doctrine -> ModeName -> GenName -> IO GenDecl
lookupGenDecl doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing ->
      assertFailure
        ( "missing generator "
            <> show name
            <> " in mode "
            <> show mode
        )
        >> fail "unreachable"
    Just gen -> pure gen


requireEither :: Either T.Text a -> IO a
requireEither (Left err) = assertFailure (T.unpack err) >> fail "unreachable"
requireEither (Right x) = pure x
