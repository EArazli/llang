{-# LANGUAGE OverloadedStrings #-}
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
import Strat.Kernel.Syntax (Term, ScopeId(..))
import Strat.Kernel.Term
import Strat.Kernel.Types
import Strat.Kernel.Unify (match)
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Ord (comparing)
import qualified Data.Text as T

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
      let freshRule = freshenRule term rule
      in
      [ Redex
          { redexStep = Step (ruleId rule) pos subst
          , redexFrom = term
          , redexTo   = newTerm
          , redexRuleIx = ruleIx rule
          }
      | pos <- positions term
      , Just sub <- [subtermAt term pos]
      , Just subst <- [match (lhs freshRule) sub]
      , Just newTerm <- [replaceAtChecked (rsSig rs) term pos (applySubstTerm subst (rhs freshRule))]
      ]

applyStep :: RewriteSystem -> Step -> Term -> Maybe Term
applyStep rs step term = do
  let baseRule = getRule rs (stepRule step)
  let rule = freshenRule term baseRule
  sub <- subtermAt term (stepPos step)
  let lhs' = applySubstTerm (stepSubst step) (lhs rule)
  if lhs' /= sub
    then Nothing
    else replaceAtChecked (rsSig rs) term (stepPos step) (applySubstTerm (stepSubst step) (rhs rule))

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

freshenRule :: Term -> Rule -> Rule
freshenRule term rule =
  let used = scopesInTerm term
      ruleScopes = scopesInTerm (lhs rule) `S.union` scopesInTerm (rhs rule)
      (mapping, _) = S.foldl' assign (M.empty, used) ruleScopes
  in rule
      { lhs = renameWith mapping (lhs rule)
      , rhs = renameWith mapping (rhs rule)
      }
  where
    assign (m, used) old =
      let rid = ruleId rule
          base = "rw:" <> ridEq rid <> ":" <> T.pack (show (ridDir rid)) <> ":"
          newScope = freshScope used base 0
      in (M.insert old newScope m, S.insert newScope used)

    freshScope :: S.Set ScopeId -> T.Text -> Int -> ScopeId
    freshScope used base ix =
      let candidate = ScopeId (base <> T.pack (show ix))
      in if candidate `S.member` used
           then freshScope used base (ix + 1)
           else candidate

    renameWith m tm =
      S.foldl'
        (\acc old -> case M.lookup old m of
            Nothing -> acc
            Just new -> renameScope old new acc)
        tm
        (S.fromList (M.keys m))

normalize :: Int -> RewriteSystem -> Term -> Term
normalize = normalizeWith FirstRedex
