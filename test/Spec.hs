module Main (main) where

import Test.Tasty
import qualified Test.CLI.Golden as CLIGolden
import qualified Test.NoPolyPrefixes as NoPolyPrefixes
import qualified Test.Poly.Basic as PolyBasic
import qualified Test.Poly.Rewrite as PolyRewrite
import qualified Test.Poly.DSL as PolyDSL
import qualified Test.Poly.Morphism as PolyMorphism
import qualified Test.Poly.Eval as PolyEval
import qualified Test.Poly.Pushout as PolyPushout
import qualified Test.Poly.Coherence as PolyCoherence
import qualified Test.Poly.CCC as PolyCCC
import qualified Test.Poly.Surface as PolySurface
import qualified Test.Poly.STLCSurface as PolySTLCSurface
import qualified Test.Poly.NoLegacy as PolyNoLegacy
import qualified Test.Poly.StdlibCoherence as PolyStdlibCoherence

main :: IO ()
main =
  defaultMain $
    testGroup
      "All"
      [ CLIGolden.tests
      , PolyBasic.tests
      , PolyRewrite.tests
      , PolyDSL.tests
      , PolyMorphism.tests
      , PolyEval.tests
      , PolyPushout.tests
      , PolyCoherence.tests
      , PolyCCC.tests
      , PolySurface.tests
      , PolySTLCSurface.tests
      , PolyNoLegacy.tests
      , PolyStdlibCoherence.tests
      , NoPolyPrefixes.tests
      ]
