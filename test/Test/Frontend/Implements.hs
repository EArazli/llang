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
import Strat.Kernel.Morphism (morName, morSrc, morTgt)
import qualified Data.Map.Strict as M
import qualified Data.Text as T


tests :: TestTree
tests =
  testGroup
    "Frontend.Implements"
    [ testCase "explicit run implements wins" testExplicitWins
    , testCase "declared default is used" testDeclaredDefault
    , testCase "colliding defaults resolve by match" testDefaultCollisionSelectsMatch
    , testCase "ambiguous default error" testAmbiguousDefault
    , testCase "unique candidate fallback" testUniqueCandidate
    , testCase "ambiguous implementation error" testAmbiguous
    , testCase "identity fallback when interface matches run doctrine" testIdentityFallback
    , testCase "identity not used on name collision" testNameCollisionNoIdentity
    , testCase "mismatched default does not block candidate" testDefaultMismatchFallback
    ]


baseEnv :: IO ModuleEnv
baseEnv =
  envFromSrc $ T.unlines
    [ "doctrine I where { sort Obj; op a : Obj; }"
    , "doctrine D where { sort Obj; op a : Obj; }"
    , "morphism m1 : I -> D where { sort Obj = Obj; op a = a; }"
    , "morphism m2 : I -> D where { sort Obj = Obj; op a = a; }"
    ]

envFromSrc :: T.Text -> IO ModuleEnv
envFromSrc src =
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
  let env = env0 { meImplDefaults = M.insert (presName presI, presName presD) ["m1"] (meImplDefaults env0) }
  let surf = mkSurface presI
  let res = buildMorphismEnv env presD surf []
  case res of
    Left err -> assertFailure (T.unpack err)
    Right morphs ->
      case M.lookup "i" morphs of
        Nothing -> assertFailure "missing morphism"
        Just mor -> morName mor @?= "m1"

testDefaultCollisionSelectsMatch :: Assertion
testDefaultCollisionSelectsMatch = do
  let src = T.unlines
        [ "doctrine A where { sort Obj; op a : Obj; }"
        , "doctrine B = rename ops { A.a -> A.a2 } in A;"
        , "doctrine C where { sort Obj; op c : Obj; }"
        , "doctrine D = rename ops { C.c -> C.c2 } in C;"
        , "morphism mAC : A -> C where { sort Obj = Obj; op a = c; }"
        , "morphism mAC2 : A -> C where { sort Obj = Obj; op a = c; }"
        , "morphism mBD : B -> D where { sort Obj = Obj; op a2 = c2; }"
        , "morphism mBD2 : B -> D where { sort Obj = Obj; op a2 = c2; }"
        , "implements A for C using mAC;"
        , "implements B for D using mBD;"
        ]
  env <- envFromSrc src
  presA <- requirePres env "A"
  presB <- requirePres env "B"
  presC <- requirePres env "C"
  presD <- requirePres env "D"
  presName presA @?= presName presB
  presName presC @?= presName presD
  assertBool "expected A and B presentations to differ" (presA /= presB)
  assertBool "expected C and D presentations to differ" (presC /= presD)
  let surfA = mkSurface presA
  let resA = buildMorphismEnv env presC surfA []
  case resA of
    Left err -> assertFailure (T.unpack err)
    Right morphs ->
      case M.lookup "i" morphs of
        Nothing -> assertFailure "missing morphism"
        Just mor -> morName mor @?= "mAC"
  let surfB = mkSurface presB
  let resB = buildMorphismEnv env presD surfB []
  case resB of
    Left err -> assertFailure (T.unpack err)
    Right morphs ->
      case M.lookup "i" morphs of
        Nothing -> assertFailure "missing morphism"
        Just mor -> morName mor @?= "mBD"

testAmbiguousDefault :: Assertion
testAmbiguousDefault = do
  let src = T.unlines
        [ "doctrine I where { sort Obj; op a : Obj; }"
        , "doctrine D where { sort Obj; op a : Obj; }"
        , "morphism m1 : I -> D where { sort Obj = Obj; op a = a; }"
        , "morphism m2 : I -> D where { sort Obj = Obj; op a = a; }"
        , "implements I for D using m1;"
        , "implements I for D using m2;"
        ]
  env <- envFromSrc src
  presI <- requirePres env "I"
  presD <- requirePres env "D"
  let surf = mkSurface presI
  let res = buildMorphismEnv env presD surf []
  case res of
    Left err -> err @?= "Ambiguous default implements for alias: i"
    Right _ -> assertFailure "expected ambiguous default error"

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

testIdentityFallback :: Assertion
testIdentityFallback = do
  env <- envFromSrc "doctrine D where { sort Obj; op a : Obj; }"
  presD <- requirePres env "D"
  let surf = mkSurface presD
  let res = buildMorphismEnv env presD surf []
  case res of
    Left err -> assertFailure (T.unpack err)
    Right morphs ->
      case M.lookup "i" morphs of
        Nothing -> assertFailure "missing morphism"
        Just mor -> do
          morName mor @?= "identity"
          morSrc mor @?= presD
          morTgt mor @?= presD

testNameCollisionNoIdentity :: Assertion
testNameCollisionNoIdentity = do
  let src = T.unlines
        [ "doctrine X where { sort Obj; op a : Obj; }"
        , "doctrine Y = rename ops { X.a -> X.a2 } in X;"
        ]
  env <- envFromSrc src
  presX <- requirePres env "X"
  presY <- requirePres env "Y"
  presName presX @?= presName presY
  assertBool "expected X and Y presentations to differ" (presX /= presY)
  let surf = mkSurface presX
  let res = buildMorphismEnv env presY surf []
  case res of
    Left err -> err @?= "Missing implementation for alias: i"
    Right _ -> assertFailure "expected missing implementation error"

testDefaultMismatchFallback :: Assertion
testDefaultMismatchFallback = do
  let src = T.unlines
        [ "doctrine X where { sort Obj; op a : Obj; }"
        , "doctrine Y = rename ops { X.a -> X.a2 } in X;"
        , "morphism mXY : X -> Y where { op a = a2; }"
        , "morphism mBad : X -> X where { op a = a; }"
        ]
  env0 <- envFromSrc src
  presX <- requirePres env0 "X"
  presY <- requirePres env0 "Y"
  let env = env0 { meImplDefaults = M.insert (presName presX, presName presY) ["mBad"] (meImplDefaults env0) }
  let surf = mkSurface presX
  let res = buildMorphismEnv env presY surf []
  case res of
    Left err -> assertFailure (T.unpack err)
    Right morphs ->
      case M.lookup "i" morphs of
        Nothing -> assertFailure "missing morphism"
        Just mor -> morName mor @?= "mXY"
