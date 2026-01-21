{-# LANGUAGE OverloadedStrings #-}
module Test.Surface2.Determinism
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Kernel.DSL.Parse (parseRawFile)
import Strat.Kernel.DSL.Elab (elabRawFile)
import Strat.Frontend.Env (ModuleEnv(..), emptyEnv)
import Strat.Surface2.Engine
import Strat.Surface2.Term (STerm(..), Con2Name(..), JudgName(..))
import Strat.Surface2.Def (SurfaceDef(..))
import qualified Data.Map.Strict as M
import qualified Data.Text as T


tests :: TestTree
tests =
  testGroup
    "Surface2.Determinism"
    [ testCase "rule order does not affect result" testRuleOrder
    , testCase "ambiguous rules detected" testAmbiguous
    ]


testRuleOrder :: Assertion
testRuleOrder = do
  let base = surfaceProgram ["rule a:", "rule b:"]
  let swapped = surfaceProgram ["rule b:", "rule a:"]
  surf1 <- loadSurface base
  surf2 <- loadSurface swapped
  let goal = [GSurf (SCon (Con2Name "A") [])]
  let res1 = solveJudgment surf1 (JudgName "J") goal 20
  let res2 = solveJudgment surf2 (JudgName "J") goal 20
  case (res1, res2) of
    (Right r1, Right r2) -> srOutputs r1 @?= srOutputs r2
    (Left err, _) -> assertFailure (T.unpack (renderSolveError err))
    (_, Left err) -> assertFailure (T.unpack (renderSolveError err))

testAmbiguous :: Assertion
testAmbiguous = do
  let prog = T.unlines
        [ "doctrine D where { }"
        , "surface S where {"
        , "  requires ccc : D;"
        , "  context_sort Ty;"
        , "  sort Ty;"
        , "  sort Tm;"
        , "  con A : Tm;"
        , "  judgement J : (t:Tm) => (e:Core);"
        , "  rule a:"
        , "    --------------------------------"
        , "    J(A) => c1;"
        , "  rule b:"
        , "    --------------------------------"
        , "    J(A) => c2;"
        , "}"
        ]
  surf <- loadSurface prog
  let goal = [GSurf (SCon (Con2Name "A") [])]
  case solveJudgment surf (JudgName "J") goal 20 of
    Left (AmbiguousRules {}) -> pure ()
    Left err -> assertFailure ("expected AmbiguousRules, got " <> T.unpack (renderSolveError err))
    Right _ -> assertFailure "expected ambiguity error"


surfaceProgram :: [T.Text] -> T.Text
surfaceProgram ruleLines =
  T.unlines $
    [ "doctrine D where { }"
    , "surface S where {"
    , "  requires ccc : D;"
    , "  context_sort Ty;"
    , "  sort Ty;"
    , "  sort Tm;"
    , "  con A : Tm;"
    , "  con B : Tm;"
    , "  judgement J : (t:Tm) => (e:Core);"
    ] <>
    ruleBlock ruleLines <>
    [ "}"
    ]
  where
    ruleBlock names =
      concatMap mkRule names

    mkRule nameLine =
      case nameLine of
        "rule a:" ->
          [ "  rule a:"
          , "    --------------------------------"
          , "    J(A) => c1;"
          ]
        "rule b:" ->
          [ "  rule b:"
          , "    --------------------------------"
          , "    J(B) => c2;"
          ]
        other -> [other]

loadSurface :: T.Text -> IO SurfaceDef
loadSurface src =
  case parseRawFile src of
    Left err -> assertFailure (T.unpack err) >> pure (error "parse")
    Right rf ->
      case elabRawFile rf of
        Left err -> assertFailure (T.unpack err) >> pure (error "elab")
        Right env ->
          case M.lookup "S" (meSurfaces env) of
            Nothing -> assertFailure "missing surface S" >> pure (error "missing")
            Just s -> pure s
