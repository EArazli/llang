{-# LANGUAGE OverloadedStrings #-}
module Test.CLI.Golden
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.CLI (runCLI, CLIOptions(..))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (getTemporaryDirectory, removeFile)
import System.FilePath ((</>))
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "CLI.Golden"
    [ testCase "planar_monoid.run.llang output" (goldenRun "examples/run/algebra/planar_monoid.run.llang" expectedPlanarMonoid)
    , testCase "cart_monoid.run.llang output" (goldenRun "examples/run/algebra/cart_monoid.run.llang" expectedCartMonoid)
    , testCase "box_match.run.llang output" (goldenRun "examples/run/algebra/box_match.run.llang" expectedBoxMatch)
    , testCase "coherence_demo.run.llang output" (goldenRun "examples/run/algebra/coherence_demo.run.llang" expectedCoherenceDemo)
    , testCase "loop_demo.run.llang output" (goldenRun "examples/run/algebra/loop_demo.run.llang" expectedLoopDemo)
    , testCase "mode_map_demo.run.llang output" (goldenRun "examples/run/algebra/mode_map_demo.run.llang" expectedModeMapDemo)
    , testCase "hello_world.run.llang output" (goldenRun "examples/run/algebra/hello_world.run.llang" expectedHelloWorld)
    , testCase "minifun.concat2.run.llang output" (goldenRun "examples/run/codegen/minifun/concat2.run.llang" expectedMiniFunConcat2)
    , testCase "server_targets.run.llang bun output" (goldenRunNamed "examples/run/codegen/server_targets.run.llang" "bun" expectedServerTargetBun)
    , testCase "server_targets.run.llang express output" (goldenRunNamed "examples/run/codegen/server_targets.run.llang" "express" expectedServerTargetExpress)
    , testCase "arith_targets.run.llang js output" (goldenRunNamed "examples/run/codegen/arith_targets.run.llang" "js" expectedArithTargetJs)
    , testCase "arith_targets.run.llang c output" (goldenRunNamed "examples/run/codegen/arith_targets.run.llang" "c" expectedArithTargetC)
    , testCase "term_ref.run.llang output" (goldenRun "examples/run/terms/term_ref.run.llang" expectedTermRef)
    , testCase "dual_discipline_surface linear error includes generator and mode" testDualDisciplineLinearError
    , testCase "surface unknown generator error includes generator and mode" testSurfaceUnknownGeneratorError
    ]


goldenRun :: FilePath -> Text -> Assertion
goldenRun relPath expected = do
  path <- getDataFileName relPath
  result <- runCLI (CLIOptions path Nothing)
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> out @?= expected

goldenRunNamed :: FilePath -> Text -> Text -> Assertion
goldenRunNamed relPath runName expected = do
  path <- getDataFileName relPath
  result <- runCLI (CLIOptions path (Just runName))
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> out @?= expected

testDualDisciplineLinearError :: Assertion
testDualDisciplineLinearError = do
  path <- getDataFileName "examples/run/modes/dual_discipline_surface.run.llang"
  result <- runCLI (CLIOptions path (Just "linear"))
  case result of
    Left err -> do
      assertBool "expected unknown generator prefix" ("run: unknown generator:" `T.isInfixOf` err)
      assertBool "expected generator name in error" ("dup" `T.isInfixOf` err)
      assertBool "expected mode name in error" ("Lin" `T.isInfixOf` err)
    Right out -> assertFailure ("expected linear run to fail, got output:\n" <> T.unpack out)

testSurfaceUnknownGeneratorError :: Assertion
testSurfaceUnknownGeneratorError = do
  tmpDir <- getTemporaryDirectory
  let path = tmpDir </> "llang-surface-unknown-generator.run.llang"
  TIO.writeFile path surfaceUnknownGeneratorRun
  result <- runCLI (CLIOptions path Nothing)
  _ <- removeFile path
  case result of
    Left err -> do
      assertBool "expected surface unknown generator prefix" ("run: surface: unknown generator:" `T.isInfixOf` err)
      assertBool "expected generator name in error" ("nope" `T.isInfixOf` err)
      assertBool "expected mode name in error" ("M" `T.isInfixOf` err)
    Right out -> assertFailure ("expected run to fail, got output:\n" <> T.unpack out)

surfaceUnknownGeneratorRun :: Text
surfaceUnknownGeneratorRun =
  T.unlines
    [ "doctrine D where {"
    , "  mode M;"
    , "  structure M = linear;"
    , "  type A @M;"
    , "  gen f : [M.A] -> [M.A] @M;"
    , "}"
    , "surface S where {"
    , "  doctrine D;"
    , "  mode M;"
    , "  lexer {"
    , "    keywords: diag, in, out;"
    , "    symbols: \"(\", \")\", \"{\", \"}\", \":\", \";\", \",\";"
    , "  }"
    , "  expr {"
    , "    atom:"
    , "      ident(name) \"(\" <expr> \")\" => $1 ; #name"
    , "    | ident(name) => $name"
    , "    | \"out\" <expr> => $1"
    , "    | \"diag\" \"{\" <expr> \"}\" => $1"
    , "    | \"(\" <expr> \")\" => <expr>"
    , "    ;"
    , "    prefix:"
    , "      \"in\" ident(name) \":\" <type>(ty) \";\" <expr> => <expr> bind in(name, ty, 1)"
    , "    ;"
    , "    infixr 10 \",\" => $1 * $2;"
    , "  }"
    , "}"
    , "run main where {"
    , "  doctrine D;"
    , "  mode M;"
    , "  surface S;"
    , "  show normalized;"
    , "}"
    , "---"
    , "diag {"
    , "  in x:M.A;"
    , "  out nope(x)"
    , "}"
    , "---"
    ]

expectedPlanarMonoid :: Text
expectedPlanarMonoid =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
    , "ixctx: []"
    , "in: []"
    , "out: [p0:M.A]"
    , "edges:"
    , "  e0: unit [] -> [p0]"
    ]

expectedCartMonoid :: Text
expectedCartMonoid =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
    , "ixctx: []"
    , "in: [p0:M.A]"
    , "out: [p1:M.A]"
    , "edges:"
    , "  e0: mul [p2, p3] -> [p1]"
    , "  e1: dup [p0] -> [p2, p3]"
    ]

expectedBoxMatch :: Text
expectedBoxMatch =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
    , "ixctx: []"
    , "in: [p0:M.A]"
    , "out: [p1:M.A]"
    , "edges:"
    , "  e0: box B [p0] -> [p1]"
    , "    mode: M"
    , "    ixctx: []"
    , "    in: [p0:M.A]"
    , "    out: [p1:M.A]"
    , "    edges:"
    , "      e0: g [p0] -> [p1]"
    ]

expectedCoherenceDemo :: Text
expectedCoherenceDemo =
  T.intercalate "\n"
    [ "coherence:"
    , "  obligations: 1"
    , "  join: 1"
    , "  commute: 0"
    , "  failures: 1"
    , ""
    , "  failure 1: s.lr vs c.lr (NeedsJoin)"
    , "  overlap:"
    , "    mode: M"
    , "    ixctx: []"
    , "    in: [p0:M.A]"
    , "    out: [p1:M.A]"
    , "    edges:"
    , "      e0: f [p0] -> [p1]"
    , "  left:"
    , "    mode: M"
    , "    ixctx: []"
    , "    in: [p0:M.A]"
    , "    out: [p0:M.A]"
    , "    edges:"
    , "  right:"
    , "    mode: M"
    , "    ixctx: []"
    , "    in: [p0:M.A]"
    , "    out: [p1:M.A]"
    , "    edges:"
    , "      e0: g [p0] -> [p1]"
    ]

expectedLoopDemo :: Text
expectedLoopDemo =
  T.intercalate "\n"
    [ "value:"
    , "VList [VAtom \"letrec\",VList [VList [VAtom \"$p0\",VList [VAtom \"dup#1\",VAtom \"$p2\"]],VList [VAtom \"$p1\",VList [VAtom \"dup#0\",VAtom \"$p2\"]],VList [VAtom \"$p2\",VList [VAtom \"f\",VAtom \"$p1\"]]],VAtom \"$p0\"]"
    ]

expectedTermRef :: Text
expectedTermRef =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
    , "ixctx: []"
    , "in: [p0:M.A]"
    , "out: [p1:M.A]"
    , "edges:"
    , "  e0: f [p0] -> [p2]"
    , "  e1: g [p2] -> [p1]"
    ]

expectedModeMapDemo :: Text
expectedModeMapDemo =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: V"
    , "ixctx: []"
    , "in: [p0:V.B]"
    , "out: [p1:V.B]"
    , "edges:"
    , "  e0: g [p0] -> [p1]"
    ]

expectedHelloWorld :: Text
expectedHelloWorld =
  T.intercalate "\n"
    [ "value:"
    , "Hello, world!"
    ]

expectedMiniFunConcat2 :: Text
expectedMiniFunConcat2 =
  T.intercalate "\n"
    [ "value:"
    , "const fs = require(\"fs\");"
    , "const input = fs.readFileSync(0, \"utf8\").split(\"\\n\");"
    , "let i = 0;"
    , "function nextLine() { return input[i++]; }"
    , "console.log((nextLine() + nextLine()));"
    ]

expectedServerTargetBun :: Text
expectedServerTargetBun =
  T.intercalate "\n"
    [ "value:"
    , "(() => {"
    , "  const p5 = \"!\";"
    , "  const p2 = \", \";"
    , "  const world = \"world\";"
    , "  const hello = \"Hello\";"
    , "  const p3 = hello + p2;"
    , "  const p4 = p3 + world;"
    , "  const msg = p4 + p5;"
    , "  Bun.serve({ fetch(req) { return new Response(msg); } });"
    , "})()"
    ]

expectedServerTargetExpress :: Text
expectedServerTargetExpress =
  T.intercalate "\n"
    [ "value:"
    , "(() => {"
    , "  const p5 = \"!\";"
    , "  const p2 = \", \";"
    , "  const world = \"world\";"
    , "  const hello = \"Hello\";"
    , "  const p3 = hello + p2;"
    , "  const p4 = p3 + world;"
    , "  const msg = p4 + p5;"
    , "  const app = require(\"express\")(); app.get(\"/\", (_req, res) => res.send(msg)); app.listen(3000);"
    , "})()"
    ]

expectedArithTargetJs :: Text
expectedArithTargetJs =
  T.intercalate "\n"
    [ "value:"
    , "(() => {"
    , "  const p3 = 3;"
    , "  const p2 = 2;"
    , "  const p4 = (p2 * p3);"
    , "  const p1 = 1;"
    , "  const p0 = (p1 + p4);"
    , "  return p0;"
    , "})()"
    ]

expectedArithTargetC :: Text
expectedArithTargetC =
  T.intercalate "\n"
    [ "value:"
    , "int main() {"
    , "  int p3 = 3;"
    , "  int p2 = 2;"
    , "  int p4 = (p2 * p3);"
    , "  int p1 = 1;"
    , "  int p0 = (p1 + p4);"
    , "  return p0;"
    , "}"
    ]
