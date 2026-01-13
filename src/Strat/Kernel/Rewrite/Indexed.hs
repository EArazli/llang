{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Rewrite.Indexed
  ( RuleIndex
  , buildRuleIndex
  , rewriteOnceIndexed
  ) where

import Strat.Kernel.Rule
import Strat.Kernel.Rewrite
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Subst (applySubstTerm)
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import Strat.Kernel.Types
import Strat.Kernel.Unify (match)
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Ord (comparing)
import qualified Data.Text as T

data RuleIndex = RuleIndex
  { riByOp   :: M.Map OpName [Rule]
  , riVarRoot :: [Rule]
  }

buildRuleIndex :: RewriteSystem -> RuleIndex
buildRuleIndex rs =
  foldl addRule (RuleIndex M.empty []) (rulesInOrder rs)
  where
    addRule idx r =
      case termNode (lhs r) of
        TVar _ -> idx { riVarRoot = riVarRoot idx <> [r] }
        TOp op _ ->
          let byOp = M.insertWith (\new old -> old <> new) op [r] (riByOp idx)
          in idx { riByOp = byOp }

rewriteOnceIndexed :: RewriteSystem -> RuleIndex -> Term -> [Redex]
rewriteOnceIndexed rs idx term =
  L.sortBy (comparing redexKey) (concatMap redexesAt (positions term))
  where
    redexKey r = (redexRuleIx r, stepPos (redexStep r))

    redexesAt pos =
      case subtermAt term pos of
        Nothing -> []
        Just sub ->
          let candidates =
                case termNode sub of
                  TVar _ -> riVarRoot idx
                  TOp op _ -> riVarRoot idx <> M.findWithDefault [] op (riByOp idx)
          in
          [ Redex
              { redexStep = Step (ruleId rule) pos subst
              , redexFrom = term
              , redexTo = newTerm
              , redexRuleIx = ruleIx rule
              }
          | rule <- candidates
          , let freshRule = freshenRule term rule
          , Just subst <- [match (lhs freshRule) sub]
          , Just newTerm <- [replaceAtChecked (rsSig rs) term pos (applySubstTerm subst (rhs freshRule))]
          ]

    freshenRule t rule =
      let used = scopesInTerm t
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
