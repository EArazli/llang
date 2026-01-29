{-# LANGUAGE OverloadedStrings #-}
module Test.CLI
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.Frontend.Run
import Strat.CLI (runCLI, CLIOptions(..))
import Strat.Backend (Value(..))
import Strat.Backend.Concat (CatExpr(..))
import Strat.Kernel.Syntax (OpName(..), Term(..), TermNode(..))
import Data.Text (Text)
import qualified Data.Text as T
import Paths_llang (getDataFileName)
import System.Directory (createDirectoryIfMissing, removePathForcibly, getTemporaryDirectory)
import System.FilePath ((</>))
import qualified Data.Text.IO as TIO
import System.IO.Error (catchIOError)


tests :: TestTree
tests =
  testGroup
    "CLI"
    [ testCase "end-to-end monoid" testEndToEndMonoid
    , testCase "end-to-end monoid alt syntax/model" testEndToEndMonoidAlt
    , testCase "end-to-end peano" testEndToEndPeano
    , testCase "end-to-end pushout model restriction nat_bool" testEndToEndNatBoolRestriction
    , testCase "end-to-end ski" testEndToEndSKI
    , testCase "end-to-end category" testEndToEndCat
    , testCase "end-to-end STLC surface" testEndToEndSTLCSurface
    , testCase "end-to-end STLC surface lam" testEndToEndSTLCLam
    , testCase "end-to-end STLC surface lam nested x" testEndToEndSTLCLamNestedX
    , testCase "end-to-end STLC surface lam nested y" testEndToEndSTLCLamNestedY
    , testCase "end-to-end STLC surface pair/fst" testEndToEndSTLCPair
    , testCase "end-to-end STLC surface unknown identifier" testEndToEndSTLCBadIdent
    , testCase "multi-run default main" testMultiRunDefault
    , testCase "multi-run selection" testMultiRunSelect
    , testCase "poly no-dup error" testPolyNoDupError
    , testCase "poly ambiguous model restriction" testPolyAmbiguousModelRestriction
    , testCase "poly cart term surface with model" testPolyCartTermModel
    , testCase "poly morphism apply" testPolyMorphismApply
    , testCase "poly run_spec default" testPolyRunSpecDefault
    , testCase "poly run_spec select" testPolyRunSpecSelect
    , testCase "poly implements uses" testPolyImplementsUses
    , testCase "poly STLC surface lam1" testPolySTLCLam1
    , testCase "poly STLC surface app1" testPolySTLCApp1
    , testCase "poly STLC surface pair1" testPolySTLCPair1
    ]


testEndToEndMonoid :: Assertion
testEndToEndMonoid = do
  path <- getDataFileName "examples/monoid.run.llang"
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      rrCatExpr out @?= CatOp (OpName "Combined.e") []
      rrValue out @?= VString ""
      rrPrintedNormalized out @?= "e"

testEndToEndMonoidAlt :: Assertion
testEndToEndMonoidAlt = do
  path <- getDataFileName "examples/monoid.alt.run.llang"
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      rrValue out @?= VInt 0
      rrPrintedNormalized out @?= "unit"


testEndToEndPeano :: Assertion
testEndToEndPeano = do
  path <- getDataFileName "examples/peano.run.llang"
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> rrValue out @?= VInt 6

testEndToEndNatBoolRestriction :: Assertion
testEndToEndNatBoolRestriction = do
  path <- getDataFileName "examples/pushout/nat_bool.run.llang"
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> rrValue out @?= VInt 1


testEndToEndSKI :: Assertion
testEndToEndSKI = do
  path <- getDataFileName "examples/ski.run.llang"
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> rrValue out @?= VAtom "SKI.a"


testEndToEndCat :: Assertion
testEndToEndCat = do
  path <- getDataFileName "examples/cat.run.llang"
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      let ops = collectOps (rrNormalized out)
      assertBool "no id in normal form" (OpName "Cat.id" `notElem` ops)
      case termNode (rrNormalized out) of
        TOp (OpName "Cat.comp") [_, _, _, Term _ (TOp (OpName "Cat.h") []), Term _ (TOp (OpName "Cat.comp") innerArgs)] ->
          case innerArgs of
            [_, _, _, Term _ (TOp (OpName "Cat.g") []), Term _ (TOp (OpName "Cat.f") [])] -> pure ()
            _ -> assertFailure "inner composition not in expected form"
        _ -> assertFailure "outer composition not in expected form"

testEndToEndSTLCSurface :: Assertion
testEndToEndSTLCSurface = do
  path <- getDataFileName "examples/ccc_surface/stlc.run.llang"
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      assertBool "surface input printed" (maybe False (not . T.null) (rrPrintedInput out))
      assertHasOp "CCC.T" (rrNormalized out)
      case termNode (rrNormalized out) of
        TOp _ _ -> pure ()
        _ -> assertFailure "expected normalized core term"

testEndToEndSTLCLam :: Assertion
testEndToEndSTLCLam = do
  path <- getDataFileName "examples/ccc_surface/stlc.lam1.run.llang"
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      let ops = collectOps (rrNormalized out)
      assertBool "expected curry in core term" (OpName "CCC.curry" `elem` ops)

testEndToEndSTLCLamNestedX :: Assertion
testEndToEndSTLCLamNestedX = do
  path <- getDataFileName "examples/ccc_surface/stlc.lam2.run.llang"
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      let ops = collectOps (rrNormalized out)
      assertBool "expected curry in core term" (OpName "CCC.curry" `elem` ops)

testEndToEndSTLCLamNestedY :: Assertion
testEndToEndSTLCLamNestedY = do
  path <- getDataFileName "examples/ccc_surface/stlc.lam3.run.llang"
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      let ops = collectOps (rrNormalized out)
      assertBool "expected curry in core term" (OpName "CCC.curry" `elem` ops)

testEndToEndSTLCPair :: Assertion
testEndToEndSTLCPair = do
  path <- getDataFileName "examples/ccc_surface/stlc.pair.run.llang"
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()

testEndToEndSTLCBadIdent :: Assertion
testEndToEndSTLCBadIdent = do
  tmp <- getTemporaryDirectory
  let dir = tmp </> "llang-cli-stlc-bad"
  cleanup dir
  createDirectoryIfMissing True dir
  specPath <- getDataFileName "examples/ccc_surface/stlc.runspec.llang"
  let badFile = dir </> "bad-stlc.run.llang"
  TIO.writeFile badFile $ T.unlines
    [ "import \"" <> T.pack specPath <> "\";"
    , "run main using STLCinCCC"
    , "---"
    , "unknownIdent"
    ]
  result <- runFile badFile Nothing
  case result of
    Left _ -> pure ()
    Right _ -> assertFailure "expected failure for unknown identifier"
  cleanup dir
  where
    cleanup path = removePathForcibly path `catchIOError` \_ -> pure ()

testMultiRunDefault :: Assertion
testMultiRunDefault = do
  path <- getDataFileName "examples/runspec/multi.llang"
  result <- runFile path Nothing
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> assertHasOp "CCC.T" (rrNormalized out)

testMultiRunSelect :: Assertion
testMultiRunSelect = do
  path <- getDataFileName "examples/runspec/multi.llang"
  result <- runFile path (Just "beta")
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> assertHasOp "CCC.F" (rrNormalized out)

testPolyNoDupError :: Assertion
testPolyNoDupError = do
  path <- getDataFileName "examples/poly/no_dup_error.run.llang"
  result <- runCLI (CLIOptions path Nothing)
  case result of
    Left err ->
      assertBool "expected boundary mismatch" ("boundary mismatch" `T.isInfixOf` err)
    Right _ -> assertFailure "expected failure for no-dup example"

testPolyAmbiguousModelRestriction :: Assertion
testPolyAmbiguousModelRestriction = do
  path <- getDataFileName "examples/poly/pushout/ambiguous_model_restriction.llang"
  result <- runCLI (CLIOptions path Nothing)
  case result of
    Left err -> do
      assertBool "expected NatBool.inl in error" ("NatBool.inl" `T.isInfixOf` err)
      assertBool "expected NatToNatBoolAlt in error" ("NatToNatBoolAlt" `T.isInfixOf` err)
    Right _ -> assertFailure "expected failure for ambiguous morphism"

testPolyCartTermModel :: Assertion
testPolyCartTermModel = do
  path <- getDataFileName "examples/poly/cart_monoid.term.run.llang"
  result <- runCLI (CLIOptions path Nothing)
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      assertBool "expected value output" ("value:" `T.isInfixOf` out)
      assertBool "expected string value" ("VString" `T.isInfixOf` out)

testPolySTLCLam1 :: Assertion
testPolySTLCLam1 = do
  path <- getDataFileName "examples/poly/ccc_surface/stlc.lam1.run.llang"
  runPolyExample path

testPolySTLCApp1 :: Assertion
testPolySTLCApp1 = do
  path <- getDataFileName "examples/poly/ccc_surface/stlc.app1.run.llang"
  runPolyExample path

testPolySTLCPair1 :: Assertion
testPolySTLCPair1 = do
  path <- getDataFileName "examples/poly/ccc_surface/stlc.pair1.run.llang"
  runPolyExample path

runPolyExample :: FilePath -> Assertion
runPolyExample path = do
  result <- runCLI (CLIOptions path Nothing)
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      assertBool "expected normalized output" ("normalized:" `T.isInfixOf` out)
      pure ()

testPolyRunSpecDefault :: Assertion
testPolyRunSpecDefault = do
  path <- getDataFileName "examples/poly/runspec/multi.llang"
  result <- runCLI (CLIOptions path Nothing)
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      assertBool "expected normalized output" ("normalized:" `T.isInfixOf` out)

testPolyRunSpecSelect :: Assertion
testPolyRunSpecSelect = do
  path <- getDataFileName "examples/poly/runspec/multi.llang"
  result <- runCLI (CLIOptions path (Just "beta"))
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      assertBool "expected normalized output" ("normalized:" `T.isInfixOf` out)

testPolyMorphismApply :: Assertion
testPolyMorphismApply = do
  path <- getDataFileName "examples/poly/morphism_term.llang"
  result <- runCLI (CLIOptions path Nothing)
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      assertBool "expected normalized output" ("normalized:" `T.isInfixOf` out)
      assertBool "expected morphism to eliminate edges" (not ("e0:" `T.isInfixOf` out))

testPolyImplementsUses :: Assertion
testPolyImplementsUses = do
  path <- getDataFileName "examples/poly/implements_uses.run.llang"
  result <- runCLI (CLIOptions path Nothing)
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> do
      assertBool "expected normalized output" ("normalized:" `T.isInfixOf` out)
      assertBool "expected f edge" ("f" `T.isInfixOf` out)

collectOps :: Term -> [OpName]
collectOps tm =
  case termNode tm of
    TVar _ -> []
    TOp op args -> op : concatMap collectOps args

assertHasOp :: Text -> Term -> Assertion
assertHasOp name tm =
  let ops = collectOps tm
      target = OpName name
  in assertBool ("expected op " <> T.unpack name) (target `elem` ops)
