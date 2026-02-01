{-# LANGUAGE OverloadedStrings #-}
module Test.CLI.Golden
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Strat.CLI (runCLI, CLIOptions(..))
import Data.Text (Text)
import qualified Data.Text as T
import Paths_llang (getDataFileName)


tests :: TestTree
tests =
  testGroup
    "CLI.Golden"
    [ testCase "planar_monoid.run.llang output" (goldenRun "examples/planar_monoid.run.llang" expectedPlanarMonoid)
    , testCase "cart_monoid.run.llang output" (goldenRun "examples/cart_monoid.run.llang" expectedCartMonoid)
    , testCase "box_match.run.llang output" (goldenRun "examples/box_match.run.llang" expectedBoxMatch)
    , testCase "coherence_demo.run.llang output" (goldenRun "examples/coherence_demo.run.llang" expectedCoherenceDemo)
    , testCase "loop_demo.run.llang output" (goldenRun "examples/loop_demo.run.llang" expectedLoopDemo)
    , testCase "mode_map_demo.run.llang output" (goldenRun "examples/mode_map_demo.run.llang" expectedModeMapDemo)
    , testCase "term_ref.run.llang output" (goldenRun "examples/term_ref.run.llang" expectedTermRef)
    , testCase "stlc.lam1.run.llang output" (goldenRun "examples/ccc_surface/stlc.lam1.run.llang" expectedStlcLam)
    , testCase "stlc.app1.run.llang output" (goldenRun "examples/ccc_surface/stlc.app1.run.llang" expectedStlcApp)
    ]


goldenRun :: FilePath -> Text -> Assertion
goldenRun relPath expected = do
  path <- getDataFileName relPath
  result <- runCLI (CLIOptions path Nothing)
  case result of
    Left err -> assertFailure (T.unpack err)
    Right out -> out @?= expected

expectedPlanarMonoid :: Text
expectedPlanarMonoid =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
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
    , "in: [p0:M.A]"
    , "out: [p1:M.A]"
    , "edges:"
    , "  e0: box B [p0] -> [p1]"
    , "    mode: M"
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
    , "    in: [p0:M.A]"
    , "    out: [p1:M.A]"
    , "    edges:"
    , "      e0: f [p0] -> [p1]"
    , "  left:"
    , "    mode: M"
    , "    in: [p0:M.A]"
    , "    out: [p0:M.A]"
    , "    edges:"
    , "  right:"
    , "    mode: M"
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
    , "in: [p0:V.B]"
    , "out: [p1:V.B]"
    , "edges:"
    , "  e0: g [p0] -> [p1]"
    ]

expectedStlcLam :: Text
expectedStlcLam =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
    , "in: []"
    , "out: [p0:M.Hom(M.Unit, M.exp(M.Bool, M.Bool))]"
    , "edges:"
    , "  e0: exr [] -> [p1]"
    , "  e1: curry [p1] -> [p0]"
    ]

expectedStlcApp :: Text
expectedStlcApp =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
    , "in: []"
    , "out: [p0:M.Hom(M.Unit, M.Bool)]"
    , "edges:"
    , "  e0: T [] -> [p0]"
    , "  e1: id [] -> [p1]"
    , "  e2: drop [p1] -> []"
    ]
