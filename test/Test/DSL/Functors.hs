{-# LANGUAGE OverloadedStrings #-}
module Test.DSL.Functors
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Map.Strict as M
import qualified Data.Text as T

import Strat.DSL.Parse (parseRawFile)
import Strat.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), gdPlainDom)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..))


tests :: TestTree
tests =
  testGroup
    "DSL.Functors"
    [ testCase "apply preserves target names and maps body references via impl" testApplyPreservesTargetNames
    , testCase "apply collision renaming keeps target name and prefixes body collision" testApplyCollisionRename
    , testCase "apply without using resolves unique morphism and rejects non-unique" testApplyUsingResolution
    ]


testApplyPreservesTargetNames :: Assertion
testApplyPreservesTargetNames = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M;"
          , "  type X @M;"
          , "}"
          , "doctrine L where {"
          , "  mode M;"
          , "  type Box @M;"
          , "}"
          , "morphism impl : S -> L where {"
          , "  mode M -> M;"
          , "  type X @M -> Box @M;"
          , "}"
          , "doctrine_functor F(L : S) where {"
          , "  gen flip : [X] -> [X] @M;"
          , "}"
          , "doctrine R = apply F to L using impl;"
          ]
  env <- expectElab src
  doc <- expectDoctrine env "R"
  let mode = ModeName "M"
  let types = M.findWithDefault M.empty mode (dTypes doc)
  assertBool "expected Box type in R" (M.member (TypeName "Box") types)
  assertBool "R should not expose X type" (not (M.member (TypeName "X") types))
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected mode M generator table"
    Just table -> pure table
  flipGen <- case M.lookup (GenName "flip") gens of
    Nothing -> assertFailure "expected generator flip"
    Just g -> pure g
  let expectedTy = TCon (TypeRef mode (TypeName "Box")) []
  gdPlainDom flipGen @?= [expectedTy]
  gdCod flipGen @?= [expectedTy]


testApplyCollisionRename :: Assertion
testApplyCollisionRename = do
  let src =
        T.unlines
          [ "doctrine S where {"
          , "  mode M;"
          , "  type X @M;"
          , "}"
          , "doctrine L where {"
          , "  mode M;"
          , "  type Box @M;"
          , "  gen get : [] -> [Box] @M;"
          , "}"
          , "morphism impl : S -> L where {"
          , "  mode M -> M;"
          , "  type X @M -> Box @M;"
          , "}"
          , "doctrine_functor F(L : S) where {"
          , "  gen get : [] -> [X] @M;"
          , "}"
          , "doctrine R = apply F to L using impl;"
          ]
  env <- expectElab src
  doc <- expectDoctrine env "R"
  let mode = ModeName "M"
  gens <- case M.lookup mode (dGens doc) of
    Nothing -> assertFailure "expected mode M generator table"
    Just table -> pure table
  assertBool "target get should be preserved" (M.member (GenName "get") gens)
  let renamed = [ g | GenName g <- M.keys gens, "F_get" `T.isPrefixOf` g ]
  assertBool "expected functor-collision rename F_get*" (not (null renamed))


testApplyUsingResolution :: Assertion
testApplyUsingResolution = do
  let srcUnique =
        T.unlines
          [ "doctrine S where {"
          , "  mode M;"
          , "  type X @M;"
          , "}"
          , "doctrine L where {"
          , "  mode M;"
          , "  type Box @M;"
          , "}"
          , "morphism impl : S -> L where {"
          , "  mode M -> M;"
          , "  type X @M -> Box @M;"
          , "}"
          , "doctrine_functor F(L : S) where {"
          , "  gen flip : [X] -> [X] @M;"
          , "}"
          , "doctrine R = apply F to L;"
          ]
  envUnique <- expectElab srcUnique
  _ <- expectDoctrine envUnique "R"

  let srcAmbiguous =
        T.unlines
          [ "doctrine S where {"
          , "  mode M;"
          , "  type X @M;"
          , "}"
          , "doctrine L where {"
          , "  mode M;"
          , "  type Box @M;"
          , "}"
          , "morphism impl1 : S -> L where {"
          , "  mode M -> M;"
          , "  type X @M -> Box @M;"
          , "}"
          , "morphism impl2 : S -> L where {"
          , "  mode M -> M;"
          , "  type X @M -> Box @M;"
          , "}"
          , "doctrine_functor F(L : S) where {"
          , "  gen flip : [X] -> [X] @M;"
          , "}"
          , "doctrine R = apply F to L;"
          ]
  err <- expectElabFailure srcAmbiguous
  assertBool "expected non-unique morphism error" ("non-unique" `T.isInfixOf` err)
  assertBool "expected impl1 listed as candidate" ("impl1" `T.isInfixOf` err)
  assertBool "expected impl2 listed as candidate" ("impl2" `T.isInfixOf` err)


expectElab :: T.Text -> IO ModuleEnv
expectElab src =
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err) >> error "unreachable"
    Right raw ->
      case elabRawFile raw of
        Left err -> assertFailure (T.unpack err) >> error "unreachable"
        Right env -> pure env


expectDoctrine :: ModuleEnv -> T.Text -> IO Doctrine
expectDoctrine env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> assertFailure ("missing doctrine: " <> T.unpack name) >> error "unreachable"
    Just doc -> pure doc


expectElabFailure :: T.Text -> IO T.Text
expectElabFailure src =
  case parseRawFile src of
    Left err -> pure err
    Right raw ->
      case elabRawFile raw of
        Left err -> pure err
        Right _ -> assertFailure "expected elaboration failure" >> error "unreachable"
