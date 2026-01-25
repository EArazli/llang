module Main (main) where

import Test.Tasty
import qualified Test.Kernel.Basic as KernelBasic
import qualified Test.Kernel.RewriteSystem as KernelRewriteSystem
import qualified Test.Kernel.Rewrite as KernelRewrite
import qualified Test.Kernel.CriticalPairs as KernelCriticalPairs
import qualified Test.Kernel.CriticalPairsDependent as KernelCriticalPairsDependent
import qualified Test.Kernel.Coherence as KernelCoherence
import qualified Test.Kernel.DSL as KernelDSL
import qualified Test.Kernel.Morphism as KernelMorphism
import qualified Test.Kernel.Pushout as KernelPushout
import qualified Test.Kernel.SortCtorTele as KernelSortCtorTele
import qualified Test.Kernel.Regression as KernelRegression
import qualified Test.Kernel.FreeTele as KernelFreeTele
import qualified Test.Surface as Surface
import qualified Test.Backend as Backend
import qualified Test.CLI as CLI
import qualified Test.CLI.Golden as CLIGolden
import qualified Test.Frontend.SyntaxModel as FrontendSyntaxModel
import qualified Test.Frontend.Loader as FrontendLoader
import qualified Test.Frontend.Implements as FrontendImplements
import qualified Test.Frontend.ModelRestriction as FrontendModelRestriction
import qualified Test.Surface2.Term as Surface2Term
import qualified Test.Surface2.Pattern as Surface2Pattern
import qualified Test.Surface2.CoreEval as Surface2CoreEval
import qualified Test.Surface2.Elab as Surface2Elab
import qualified Test.Surface2.Determinism as Surface2Determinism
import qualified Test.Poly.Basic as PolyBasic
import qualified Test.Poly.Compat as PolyCompat

main :: IO ()
main =
  defaultMain $
    testGroup
      "All"
      [ KernelBasic.tests
      , KernelRewriteSystem.tests
      , KernelRewrite.tests
      , KernelCriticalPairs.tests
      , KernelCriticalPairsDependent.tests
      , KernelCoherence.tests
      , KernelDSL.tests
      , KernelMorphism.tests
      , KernelPushout.tests
      , KernelSortCtorTele.tests
      , KernelRegression.tests
      , KernelFreeTele.tests
      , Surface.tests
      , Backend.tests
      , FrontendSyntaxModel.tests
      , FrontendLoader.tests
      , FrontendImplements.tests
      , FrontendModelRestriction.tests
      , Surface2Term.tests
      , Surface2Pattern.tests
      , Surface2CoreEval.tests
      , Surface2Elab.tests
      , Surface2Determinism.tests
      , CLI.tests
      , CLIGolden.tests
      , PolyBasic.tests
      , PolyCompat.tests
      ]
