module Main (main) where

import Test.Tasty
import qualified Test.CLI.Golden as CLIGolden
import qualified Test.DSL.Effects as DSLEffects
import qualified Test.DSL.TermRefsInDecls as DSLTermRefsInDecls
import qualified Test.DSL.Templates as DSLTemplates
import qualified Test.Frontend.Coerce as FrontendCoerce
import qualified Test.NoPolyPrefixes as NoPolyPrefixes
import qualified Test.Poly.Basic as PolyBasic
import qualified Test.Poly.Rewrite as PolyRewrite
import qualified Test.Poly.DSL as PolyDSL
import qualified Test.Poly.Literals as PolyLiterals
import qualified Test.Poly.CriticalPairs as PolyCriticalPairs
import qualified Test.Poly.Morphism as PolyMorphism
import qualified Test.Poly.Eval as PolyEval
import qualified Test.Poly.FoldSSA as PolyFoldSSA
import qualified Test.Poly.Pushout as PolyPushout
import qualified Test.Poly.Coherence as PolyCoherence
import qualified Test.Poly.CCC as PolyCCC
import qualified Test.Poly.Surface as PolySurface
import qualified Test.Poly.ModeTheory as PolyModeTheory
import qualified Test.Poly.TypeModes as PolyTypeModes
import qualified Test.Poly.DataMacro as PolyDataMacro
import qualified Test.Poly.NoLegacy as PolyNoLegacy
import qualified Test.Poly.StdlibCoherence as PolyStdlibCoherence

main :: IO ()
main =
  defaultMain $
    testGroup
      "All"
      [ CLIGolden.tests
      , DSLEffects.tests
      , DSLTermRefsInDecls.tests
      , DSLTemplates.tests
      , FrontendCoerce.tests
      , PolyBasic.tests
      , PolyRewrite.tests
      , PolyDSL.tests
      , PolyLiterals.tests
      , PolyCriticalPairs.tests
      , PolyMorphism.tests
      , PolyEval.tests
      , PolyFoldSSA.foldSSATests
      , PolyPushout.tests
      , PolyCoherence.tests
      , PolyCCC.tests
      , PolyModeTheory.tests
      , PolySurface.tests
      , PolyTypeModes.tests
      , PolyDataMacro.tests
      , PolyNoLegacy.tests
      , PolyStdlibCoherence.tests
      , NoPolyPrefixes.tests
      ]
