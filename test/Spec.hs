module Main (main) where

import Test.Tasty
import qualified Test.NoPolyPrefixes as NoPolyPrefixes
import qualified Test.Poly.Basic as PolyBasic
import qualified Test.Poly.DiagramUnion as PolyDiagramUnion
import qualified Test.Poly.Rewrite as PolyRewrite
import qualified Test.Poly.CriticalPairs as PolyCriticalPairs
import qualified Test.Poly.Morphism as PolyMorphism
import qualified Test.Poly.Pushout as PolyPushout
import qualified Test.Poly.Coherence as PolyCoherence
import qualified Test.Poly.CCC as PolyCCC
import qualified Test.Poly.ModeTheory as PolyModeTheory
import qualified Test.Poly.Surface as PolySurface
import qualified Test.Poly.TypeModes as PolyTypeModes
import qualified Test.Poly.DataMacro as PolyDataMacro
import qualified Test.Poly.Dependent as PolyDependent
import qualified Test.Poly.NoLegacy as PolyNoLegacy
import qualified Test.Poly.Foliation as PolyFoliation
import qualified Test.Poly.Acyclic as PolyAcyclic
import qualified Test.Poly.Feedback as PolyFeedback
import qualified Test.Value.Doc as ValueDoc
import qualified Test.Frontend.Pipeline as FrontendPipeline
import qualified Test.Frontend.ExampleCodegen as FrontendExampleCodegen

main :: IO ()
main =
  defaultMain $
    testGroup
      "All"
      [ PolyBasic.tests
      , PolyDiagramUnion.tests
      , PolyRewrite.tests
      , PolyCriticalPairs.tests
      , PolyMorphism.tests
      , PolyPushout.tests
      , PolyCoherence.tests
      , PolyCCC.tests
      , PolyModeTheory.tests
      , PolySurface.tests
      , PolyTypeModes.tests
      , PolyDataMacro.tests
      , PolyDependent.tests
      , PolyNoLegacy.tests
      , PolyFoliation.tests
      , PolyAcyclic.tests
      , PolyFeedback.tests
      , ValueDoc.tests
      , FrontendPipeline.tests
      , FrontendExampleCodegen.tests
      , NoPolyPrefixes.tests
      ]
