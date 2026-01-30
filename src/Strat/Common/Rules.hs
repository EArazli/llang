module Strat.Common.Rules
  ( RuleClass(..)
  , Orientation(..)
  , RewritePolicy(..)
  ) where

data RuleClass = Structural | Computational
  deriving (Eq, Ord, Show)

data Orientation = LR | RL | Bidirectional | Unoriented
  deriving (Eq, Ord, Show)

data RewritePolicy
  = UseOnlyComputationalLR
  | UseStructuralAsBidirectional
  | UseAllOriented
  deriving (Eq, Show)
