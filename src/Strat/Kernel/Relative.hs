module Strat.Kernel.Relative
  ( normalizeW
  , stepR
  , normalizeR_mod_W
  ) where

import Strat.Kernel.Rewrite
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Rule
import Strat.Kernel.Syntax (Term)
import Strat.Kernel.Types (RuleClass(..))
import qualified Data.Map.Strict as M

normalizeW :: Int -> RewriteSystem -> Term -> Term
normalizeW fuel rs t =
  normalizeWith FirstRedex fuel (filterRules isStructural rs) t
  where
    isStructural r = ruleClass r == Structural

stepR :: RewriteSystem -> Term -> [Redex]
stepR rs t = rewriteOnce (filterRules isComputational rs) t
  where
    isComputational r = ruleClass r == Computational

normalizeR_mod_W :: Int -> RewriteSystem -> Term -> Term
normalizeR_mod_W fuel rs t0 = go fuel (normalizeW fuel rs t0)
  where
    rsR = filterRules (\r -> ruleClass r == Computational) rs
    go n t
      | n <= 0 = t
      | otherwise =
          case rewriteOnce rsR t of
            [] -> t
            reds ->
              case chooseRedex reds of
                Nothing -> t
                Just r  -> go (n - 1) (normalizeW fuel rs (redexTo r))

filterRules :: (Rule -> Bool) -> RewriteSystem -> RewriteSystem
filterRules p rs =
  let rules = filter p (rsRules rs)
      ruleMap = M.fromList [(ruleId r, r) | r <- rules]
  in rs { rsRules = rules, rsRuleMap = ruleMap }
