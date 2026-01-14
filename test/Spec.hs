module Main (main) where

import Test.Tasty
import qualified Test.Kernel.Basic as KernelBasic
import qualified Test.Kernel.RewriteSystem as KernelRewriteSystem
import qualified Test.Kernel.Rewrite as KernelRewrite
import qualified Test.Kernel.CriticalPairs as KernelCriticalPairs
import qualified Test.Kernel.CriticalPairsDependent as KernelCriticalPairsDependent
import qualified Test.Kernel.Coherence as KernelCoherence
import qualified Test.Kernel.DoctrineExpr as KernelDoctrineExpr
import qualified Test.Kernel.DSL as KernelDSL
import qualified Test.Kernel.Relative as KernelRelative
import qualified Test.Surface as Surface
import qualified Test.Backend as Backend

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
      , KernelDoctrineExpr.tests
      , KernelDSL.tests
      , KernelRelative.tests
      , Surface.tests
      , Backend.tests
      ]
