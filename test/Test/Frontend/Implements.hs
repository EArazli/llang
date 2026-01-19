{-# LANGUAGE OverloadedStrings #-}
module Test.Frontend.Implements
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.DSL.Parse (parseRawFile)
import Strat.Kernel.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (ModuleEnv(..), emptyEnv)
import Strat.Frontend.Run (buildMorphismEnv)
import Strat.Surface2.Def
import Strat.Surface2.Term (Sort2Name(..))
import Strat.Kernel.DoctrineExpr (elabDocExpr)
import Strat.Kernel.Presentation
import Strat.Kernel.Signature
import Strat.Kernel.Morphism (morName)
import qualified Data.Map.Strict as M
import qualified Data.Text as T


tests :: TestTree
tests =
  testGroup
    "Frontend.Implements"
    [ testCase "explicit run implements wins" testExplicitWins
    , testCase "declared default is used" testDeclaredDefault
    , testCase "unique candidate fallback" testUniqueCandidate
    , testCase "ambiguous implementation error" testAmbiguous
    ]


baseEnv :: IO ModuleEnv
baseEnv = do
  let src = T.unlines
        [ "doctrine I where { sort Obj; op a : Obj; }"
        , "doctrine D where { sort Obj; op a : Obj; }"
        , "morphism m1 : I -> D where { sort Obj = Obj; op a = a; }"
        , "morphism m2 : I -> D where { sort Obj = Obj; op a = a; }"
        ]
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err) >> pure emptyEnv
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err) >> pure emptyEnv
        Right env -> pure env

mkSurface :: Presentation -> SurfaceDef
mkSurface pres =
  SurfaceDef
    { sdName = "S"
    , sdSorts = M.empty
    , sdContextSort = Sort2Name "Ty"
    , sdCons = M.empty
    , sdJudgments = M.empty
    , sdRules = []
    , sdDefines = M.empty
    , sdRequires = [SurfaceRequire "i" pres]
    , sdCtxDisc = CtxCartesian
    }

requirePres :: ModuleEnv -> T.Text -> IO Presentation
requirePres env name =
  case M.lookup name (meDoctrines env) of
    Nothing -> do
      assertFailure ("missing doctrine: " <> T.unpack name)
      pure (Presentation name (Signature M.empty M.empty) [])
    Just dexpr ->
      case elabDocExpr dexpr of
        Left err -> do
          assertFailure (T.unpack err)
          pure (Presentation name (Signature M.empty M.empty) [])
        Right pres -> pure pres

testExplicitWins :: Assertion
testExplicitWins = do
  env <- baseEnv
  presI <- requirePres env "I"
  presD <- requirePres env "D"
  let surf = mkSurface presI
  let res = buildMorphismEnv env presD surf [("i","m2")]
  case res of
    Left err -> assertFailure (T.unpack err)
    Right morphs ->
      case M.lookup "i" morphs of
        Nothing -> assertFailure "missing morphism"
        Just mor -> morName mor @?= "m2"

testDeclaredDefault :: Assertion
testDeclaredDefault = do
  env0 <- baseEnv
  presI <- requirePres env0 "I"
  presD <- requirePres env0 "D"
  let env = env0 { meImplDefaults = M.insert (presName presI, presName presD) "m1" (meImplDefaults env0) }
  let surf = mkSurface presI
  let res = buildMorphismEnv env presD surf []
  case res of
    Left err -> assertFailure (T.unpack err)
    Right morphs ->
      case M.lookup "i" morphs of
        Nothing -> assertFailure "missing morphism"
        Just mor -> morName mor @?= "m1"

testUniqueCandidate :: Assertion
testUniqueCandidate = do
  env0 <- baseEnv
  presI <- requirePres env0 "I"
  presD <- requirePres env0 "D"
  let env = env0 { meMorphisms = M.filterWithKey (\k _ -> k == "m1") (meMorphisms env0) }
  let surf = mkSurface presI
  let res = buildMorphismEnv env presD surf []
  case res of
    Left err -> assertFailure (T.unpack err)
    Right morphs ->
      case M.lookup "i" morphs of
        Nothing -> assertFailure "missing morphism"
        Just mor -> morName mor @?= "m1"

testAmbiguous :: Assertion
testAmbiguous = do
  env <- baseEnv
  presI <- requirePres env "I"
  presD <- requirePres env "D"
  let surf = mkSurface presI
  let res = buildMorphismEnv env presD surf []
  case res of
    Left _ -> pure ()
    Right _ -> assertFailure "expected ambiguity error"
