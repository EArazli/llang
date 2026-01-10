module Strat.Meta.Rule where

import Strat.Meta.Types
import Data.Text (Text)

data Equation t = Equation
  { eqName   :: Text
  , eqClass  :: RuleClass
  , eqOrient :: Orientation
  , eqLHS    :: t
  , eqRHS    :: t
  }
  deriving (Eq, Show)

-- Oriented rule used by the rewrite engine
-- ruleIx is deterministic iteration order only (not identity)
data Rule t = Rule
  { ruleId    :: RuleId
  , ruleIx    :: Int
  , ruleName  :: Text
  , ruleClass :: RuleClass
  , lhs       :: t
  , rhs       :: t
  }
  deriving (Eq, Show)
