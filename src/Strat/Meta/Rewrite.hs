{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Strat.Meta.Rewrite where

import Strat.Meta.Rule
import Strat.Meta.RewriteSystem
import Strat.Meta.Term.Class
import Strat.Meta.Types

data Step t = Step
  { stepRule  :: RuleId
  , stepPos   :: Pos
  , stepSubst :: Subst t
  }

data Redex t = Redex
  { redexStep :: Step t
  , redexFrom :: t
  , redexTo   :: t
  }

deriving instance (Eq t, Eq (Var t)) => Eq (Step t)
deriving instance (Show t, Show (Var t)) => Show (Step t)
deriving instance (Eq t, Eq (Var t)) => Eq (Redex t)
deriving instance (Show t, Show (Var t)) => Show (Redex t)

-- All one-step rewrites from a term
rewriteOnce :: Matchable t => RewriteSystem t -> t -> [Redex t]
rewriteOnce rs term =
  concatMap ruleRedexes (rsRules rs)
  where
    ruleRedexes rule =
      [ Redex
          { redexStep = Step (ruleId rule) pos subst
          , redexFrom = term
          , redexTo   = newTerm
          }
      | pos <- positions term
      , Just sub <- [subtermAt term pos]
      , Just subst <- [match (lhs rule) sub]
      , Just newTerm <- [replaceAt term pos (applySubst subst (rhs rule))]
      ]

applyStep :: TermLike t => (RuleId -> Rule t) -> Step t -> t -> Maybe t
applyStep lookupRuleFn step term = do
  let rule = lookupRuleFn (stepRule step)
  sub <- subtermAt term (stepPos step)
  let lhs' = applySubst (stepSubst step) (lhs rule)
  if lhs' /= sub
    then Nothing
    else replaceAt term (stepPos step) (applySubst (stepSubst step) (rhs rule))

data Strategy = FirstRedex

normalizeWith :: Matchable t => Strategy -> Int -> RewriteSystem t -> t -> t
normalizeWith strategy fuel rs t0 = go fuel t0
  where
    go n t
      | n <= 0 = t
      | otherwise =
          case strategy of
            FirstRedex ->
              case rewriteOnce rs t of
                [] -> t
                (r : _) -> go (n - 1) (redexTo r)

normalize :: Matchable t => Int -> RewriteSystem t -> t -> t
normalize = normalizeWith FirstRedex
