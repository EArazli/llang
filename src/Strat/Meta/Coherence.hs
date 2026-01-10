{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Strat.Meta.Coherence where

import Strat.Meta.CriticalPairs
import Strat.Meta.Rewrite
import Strat.Meta.RewriteSystem
import Strat.Meta.Rule
import Strat.Meta.Term.Class
import Strat.Meta.Types
import qualified Data.Map.Strict as M

data ObligationKind = NeedsJoin | NeedsCommute
  deriving (Eq, Show)

data Obligation t = Obligation
  { obKind :: ObligationKind
  , obPair :: CriticalPair t
  }

-- A joiner is a “confluence diagram”: left ->* join <-* right
data Joiner t = Joiner
  { joinTerm        :: t
  , leftDerivation  :: [Step t]
  , rightDerivation :: [Step t]
  }

deriving instance (Eq t, Eq (Var t)) => Eq (Obligation t)
deriving instance (Show t, Show (Var t)) => Show (Obligation t)
deriving instance (Eq t, Eq (Var t)) => Eq (Joiner t)
deriving instance (Show t, Show (Var t)) => Show (Joiner t)

newtype JoinDB t = JoinDB (M.Map (RuleId, RuleId, Pos) (Joiner t))

obligationsFromCPs :: [CriticalPair t] -> [Obligation t]
obligationsFromCPs = map (Obligation NeedsJoin)

-- Validation: do the derivations actually rewrite to joinTerm?
validateJoiner
  :: Matchable t
  => (RuleId -> Rule t)
  -> RewriteSystem t
  -> CriticalPair t
  -> Joiner t
  -> Bool
validateJoiner lookupRuleFn _rs cp joiner =
  case (applySteps (cpLeft cp) (leftDerivation joiner), applySteps (cpRight cp) (rightDerivation joiner)) of
    (Just lfinal, Just rfinal) ->
      lfinal == joinTerm joiner && rfinal == joinTerm joiner
    _ -> False
  where
    applySteps t steps = foldl step (Just t) steps
    step acc s = acc >>= applyStep lookupRuleFn s
