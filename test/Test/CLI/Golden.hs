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
    [ testCase "planar_monoid.run.llang output" (goldenRun "examples/poly/planar_monoid.run.llang" expectedPlanarMonoid)
    , testCase "cart_monoid.run.llang output" (goldenRun "examples/poly/cart_monoid.run.llang" expectedCartMonoid)
    , testCase "box_match.run.llang output" (goldenRun "examples/poly/box_match.run.llang" expectedBoxMatch)
    , testCase "coherence_demo.run.llang output" (goldenRun "examples/poly/coherence_demo.run.llang" expectedCoherenceDemo)
    , testCase "loop_demo.run.llang output" (goldenRun "examples/poly/loop_demo.run.llang" expectedLoopDemo)
    , testCase "stlc.lam1.run.llang output" (goldenRun "examples/poly/ccc_surface/stlc.lam1.run.llang" expectedStlcLam)
    , testCase "stlc.app1.run.llang output" (goldenRun "examples/poly/ccc_surface/stlc.app1.run.llang" expectedStlcApp)
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
    , "out: [p0:A]"
    , "edges:"
    , "  e0: unit [] -> [p0]"
    ]

expectedCartMonoid :: Text
expectedCartMonoid =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
    , "in: [p0:A]"
    , "out: [p1:A]"
    , "edges:"
    , "  e0: mul [p2, p3] -> [p1]"
    , "  e1: dup [p0] -> [p2, p3]"
    ]

expectedBoxMatch :: Text
expectedBoxMatch =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
    , "in: [p0:A]"
    , "out: [p1:A]"
    , "edges:"
    , "  e0: box B [p0] -> [p1]"
    , "    mode: M"
    , "    in: [p0:A]"
    , "    out: [p1:A]"
    , "    edges:"
    , "      e0: g [p0] -> [p1]"
    ]

expectedCoherenceDemo :: Text
expectedCoherenceDemo =
  T.intercalate "\n"
    [ "coherence:"
    , "  obligations: 2"
    , "  join: 2"
    , "  commute: 0"
    , "  failures: 2"
    , ""
    , "  failure 1: s.lr vs c.lr (NeedsJoin)"
    , "  overlap:"
    , "    mode: M"
    , "    in: [p0:A]"
    , "    out: [p1:A]"
    , "    edges:"
    , "      e0: f [p0] -> [p1]"
    , "  left:"
    , "    mode: M"
    , "    in: [p0:A]"
    , "    out: [p0:A]"
    , "    edges:"
    , "  right:"
    , "    mode: M"
    , "    in: [p0:A]"
    , "    out: [p1:A]"
    , "    edges:"
    , "      e0: g [p0] -> [p1]"
    , ""
    , "  failure 2: c.lr vs s.lr (NeedsJoin)"
    , "  overlap:"
    , "    mode: M"
    , "    in: [p0:A]"
    , "    out: [p1:A]"
    , "    edges:"
    , "      e0: f [p0] -> [p1]"
    , "  left:"
    , "    mode: M"
    , "    in: [p0:A]"
    , "    out: [p1:A]"
    , "    edges:"
    , "      e0: g [p0] -> [p1]"
    , "  right:"
    , "    mode: M"
    , "    in: [p0:A]"
    , "    out: [p0:A]"
    , "    edges:"
    ]

expectedLoopDemo :: Text
expectedLoopDemo =
  T.intercalate "\n"
    [ "value:"
    , "VList [VAtom \"letrec\",VList [VList [VAtom \"$p0\",VAtom \"$p2\"],VList [VAtom \"$p1\",VAtom \"dup\"],VList [VAtom \"$p2\",VList [VAtom \"f\",VAtom \"$p1\"]]],VAtom \"$p0\"]"
    ]

expectedStlcLam :: Text
expectedStlcLam =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
    , "in: [p0:Hom(prod(Unit, Bool), Bool)]"
    , "out: [p1:Hom(Unit, exp(Bool, Bool))]"
    , "edges:"
    , "  e0: curry [p0] -> [p1]"
    ]

expectedStlcApp :: Text
expectedStlcApp =
  T.intercalate "\n"
    [ "normalized:"
    , "mode: M"
    , "in: [p0:Hom(prod(Unit, Bool), Bool)]"
    , "out: [p1:Hom(Unit, Bool)]"
    , "edges:"
    , "  e0: T [] -> [p2]"
    , "  e1: id [] -> [p3]"
    , "  e2: pair [p3, p2] -> [p4]"
    , "  e3: comp [p0, p4] -> [p1]"
    ]
