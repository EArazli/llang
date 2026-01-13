module Strat.Kernel.Rule where

import Strat.Kernel.Syntax
import Strat.Kernel.Types
import Data.Text (Text)

data Equation = Equation
  { eqName   :: Text
  , eqClass  :: RuleClass
  , eqOrient :: Orientation
  , eqTele   :: [Binder]
  , eqLHS    :: Term
  , eqRHS    :: Term
  }
  deriving (Eq, Show)

-- Oriented rule used by the rewrite engine
-- ruleIx is deterministic iteration order only (not identity)
data Rule = Rule
  { ruleId    :: RuleId
  , ruleIx    :: Int
  , ruleName  :: Text
  , ruleClass :: RuleClass
  , lhs       :: Term
  , rhs       :: Term
  }
  deriving (Eq, Show)
