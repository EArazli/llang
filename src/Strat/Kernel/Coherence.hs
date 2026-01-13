{-# LANGUAGE StandaloneDeriving #-}
module Strat.Kernel.Coherence
  ( ObligationKind(..)
  , Obligation(..)
  , Joiner(..)
  , JoinDB(..)
  , obligationsFromCPs
  , relativeObligations
  , relativeObligationsForRules
  , validateJoiner
  ) where

import Strat.Kernel.CriticalPairs
import Strat.Kernel.Rewrite
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Syntax (Term)
import Strat.Kernel.Types
import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

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

relativeObligations :: RewriteSystem -> Either Text [Obligation]
relativeObligations rs = do
  cpsStruct <- criticalPairs CP_OnlyStructural (getRule rs) rs
  cpsMixed <- criticalPairs CP_StructuralVsComputational (getRule rs) rs
  let obsStruct = map (Obligation NeedsCommute) cpsStruct
  let obsMixed = map (Obligation NeedsJoin) cpsMixed
  pure (obsStruct <> obsMixed)

relativeObligationsForRules :: S.Set RuleId -> RewriteSystem -> Either Text [Obligation]
relativeObligationsForRules allowed rs = do
  cpsStruct <- criticalPairsForRules allowed CP_OnlyStructural (getRule rs) rs
  cpsMixed <- criticalPairsForRules allowed CP_StructuralVsComputational (getRule rs) rs
  let obsStruct = map (Obligation NeedsCommute) cpsStruct
  let obsMixed = map (Obligation NeedsJoin) cpsMixed
  pure (obsStruct <> obsMixed)

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
