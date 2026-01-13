{-# LANGUAGE StandaloneDeriving #-}
module Strat.Kernel.Rewrite
  ( Step(..)
  , Redex(..)
  , rewriteOnce
  , applyStep
  , Strategy(..)
  , chooseRedex
  , normalizeWith
  , normalize
  ) where

import Strat.Kernel.Rule
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Subst
import Strat.Kernel.Syntax (Term)
import Strat.Kernel.Term
import Strat.Kernel.Types
import Strat.Kernel.Unify (match)
import qualified Data.List as L
import Data.Ord (comparing)

data Step = Step
  { stepRule  :: RuleId
  , stepPos   :: Pos
  , stepSubst :: Subst
  }

data Redex = Redex
  { redexStep   :: Step
  , redexFrom   :: Term
  , redexTo     :: Term
  , redexRuleIx :: Int
  }

deriving instance Eq Step
deriving instance Show Step
deriving instance Eq Redex
deriving instance Show Redex

rewriteOnce :: RewriteSystem -> Term -> [Redex]
rewriteOnce rs term =
  concatMap ruleRedexes (rsRules rs)
  where
    ruleRedexes rule =
      [ Redex
          { redexStep = Step (ruleId rule) pos subst
          , redexFrom = term
          , redexTo   = newTerm
          , redexRuleIx = ruleIx rule
          }
      | pos <- positions term
      , Just sub <- [subtermAt term pos]
      , Just subst <- [match (lhs rule) sub]
      , Just newTerm <- [replaceAt term pos (applySubstTerm subst (rhs rule))]
      ]

applyStep :: (RuleId -> Rule) -> Step -> Term -> Maybe Term
applyStep lookupRuleFn step term = do
  let rule = lookupRuleFn (stepRule step)
  sub <- subtermAt term (stepPos step)
  let lhs' = applySubstTerm (stepSubst step) (lhs rule)
  if lhs' /= sub
    then Nothing
    else replaceAt term (stepPos step) (applySubstTerm (stepSubst step) (rhs rule))

data Strategy = FirstRedex

chooseRedex :: [Redex] -> Maybe Redex
chooseRedex [] = Nothing
chooseRedex reds =
  Just (L.minimumBy (comparing redexKey) reds)
  where
    redexKey r = (stepPos (redexStep r), redexRuleIx r)

normalizeWith :: Strategy -> Int -> RewriteSystem -> Term -> Term
normalizeWith strategy fuel rs t0 = go fuel t0
  where
    go n t
      | n <= 0 = t
      | otherwise =
          case strategy of
            FirstRedex ->
              case rewriteOnce rs t of
                [] -> t
                reds ->
                  case chooseRedex reds of
                    Nothing -> t
                    Just r  -> go (n - 1) (redexTo r)

normalize :: Int -> RewriteSystem -> Term -> Term
normalize = normalizeWith FirstRedex
