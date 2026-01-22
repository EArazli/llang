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
import Strat.Kernel.Presentation
import Strat.Kernel.Signature
import Strat.Kernel.Syntax (OpName(..), SortName(..), Sort(..))
import Strat.Kernel.Morphism (Morphism, morName, morSrc, morTgt)
import Strat.Kernel.Morphism.Util (symbolMapMorphism)
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
    Just pres -> pure pres

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
  let presA = mkPres "I" ["a"]
  let presB = mkPres "I" ["b"]
  let presC = mkPres "T" ["c"]
  let presD = mkPres "T" ["d"]
  mAC <- requireRight (mkMorphism "mAC" presA presC [("a","c")])
  mBD <- requireRight (mkMorphism "mBD" presB presD [("b","d")])
  let env =
        emptyEnv
          { meMorphisms = M.fromList [("mAC", mAC), ("mBD", mBD)]
          , meImplDefaults = M.fromList [((presName presA, presName presC), ["mAC","mBD"])]
          }
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
  let presX = mkPres "X" ["a"]
  let presY = mkPres "X" ["b"]
  presName presX @?= presName presY
  assertBool "expected X and Y presentations to differ" (presX /= presY)
  let surf = mkSurface presX
  let res = buildMorphismEnv emptyEnv presY surf []
  case res of
    Left err -> err @?= "Missing implementation for alias: i"
    Right _ -> assertFailure "expected missing implementation error"

testDefaultMismatchFallback :: Assertion
testDefaultMismatchFallback = do
  let presX = mkPres "I" ["a"]
  let presY = mkPres "T" ["a"]
  mXY <- requireRight (mkMorphism "mXY" presX presY [("a","a")])
  mBad <- requireRight (mkMorphism "mBad" presX presX [("a","a")])
  let env =
        emptyEnv
          { meMorphisms = M.fromList [("mXY", mXY), ("mBad", mBad)]
          , meImplDefaults = M.fromList [((presName presX, presName presY), ["mBad"])]
          }
  let surf = mkSurface presX
  let res = buildMorphismEnv env presY surf []
  case res of
    Left err -> assertFailure (T.unpack err)
    Right morphs ->
      case M.lookup "i" morphs of
        Nothing -> assertFailure "missing morphism"
        Just mor -> morName mor @?= "mXY"

mkPres :: T.Text -> [T.Text] -> Presentation
mkPres name ops =
  let sortName = SortName (name <> ".Obj")
      sortCtor = SortCtor { scName = sortName, scTele = [] }
      sig = Signature
        { sigSortCtors = M.fromList [(sortName, sortCtor)]
        , sigOps = M.fromList [ (OpName (name <> "." <> op), nullaryOpDecl name op) | op <- ops ]
        }
  in Presentation { presName = name, presSig = sig, presEqs = [] }

nullaryOpDecl :: T.Text -> T.Text -> OpDecl
nullaryOpDecl ns op =
  let s = Sort (SortName (ns <> ".Obj")) []
  in OpDecl { opName = OpName (ns <> "." <> op), opTele = [], opResult = s }

mkMorphism :: T.Text -> Presentation -> Presentation -> [(T.Text, T.Text)] -> Either T.Text Morphism
mkMorphism name src tgt pairs = do
  let sortMap = M.fromList [(SortName (presName src <> ".Obj"), SortName (presName tgt <> ".Obj"))]
  let opMap = M.fromList
        [ (OpName (presName src <> "." <> a), OpName (presName tgt <> "." <> b))
        | (a, b) <- pairs
        ]
  mor <- symbolMapMorphism src tgt sortMap opMap
  pure mor { morName = name }

requireRight :: Either T.Text a -> IO a
requireRight (Left err) = assertFailure (T.unpack err) >> fail "unreachable"
requireRight (Right v) = pure v
