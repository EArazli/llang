{-# LANGUAGE StandaloneDeriving #-}
module Strat.Kernel.Coherence where

import Strat.Kernel.CriticalPairs
import Strat.Kernel.Rewrite
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Syntax (Term)
import Strat.Kernel.Types
import qualified Data.Map.Strict as M

data ObligationKind = NeedsJoin | NeedsCommute
  deriving (Eq, Show)

data Obligation = Obligation
  { obKind :: ObligationKind
  , obPair :: CriticalPair
  }

data Joiner = Joiner
  { joinTerm        :: Term
  , leftDerivation  :: [Step]
  , rightDerivation :: [Step]
  }

deriving instance Eq Obligation
deriving instance Show Obligation
deriving instance Eq Joiner
deriving instance Show Joiner

newtype JoinDB = JoinDB (M.Map (RuleId, RuleId, Pos) Joiner)

obligationsFromCPs :: [CriticalPair] -> [Obligation]
obligationsFromCPs = map (Obligation NeedsJoin)

validateJoiner
  :: (RuleId -> Rule)
  -> RewriteSystem
  -> CriticalPair
  -> Joiner
  -> Bool
validateJoiner lookupRuleFn _rs cp joiner =
  case (applySteps (cpLeft cp) (leftDerivation joiner), applySteps (cpRight cp) (rightDerivation joiner)) of
    (Just lfinal, Just rfinal) ->
      lfinal == joinTerm joiner && rfinal == joinTerm joiner
    _ -> False
  where
    applySteps t steps = foldl step (Just t) steps
    step acc s = acc >>= applyStep lookupRuleFn s
