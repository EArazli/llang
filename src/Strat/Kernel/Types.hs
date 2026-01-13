module Strat.Kernel.Types
  ( RuleDir(..)
  , RuleId(..)
  , Pos
  , RuleClass(..)
  , Orientation(..)
  ) where

import Data.Text (Text)

data RuleDir = DirLR | DirRL
  deriving (Eq, Ord, Show)

data RuleId = RuleId
  { ridEq  :: Text
  , ridDir :: RuleDir
  }
  deriving (Eq, Ord, Show)

-- Tree positions: [] = root, [i,j] = child i then child j
type Pos = [Int]

data RuleClass = Structural | Computational
  deriving (Eq, Ord, Show)

data Orientation = LR | RL | Bidirectional | Unoriented
  deriving (Eq, Ord, Show)
