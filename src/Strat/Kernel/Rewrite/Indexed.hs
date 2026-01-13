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
import Strat.Kernel.Unify (match)
import qualified Data.List as L
import qualified Data.Map.Strict as M
import Data.Ord (comparing)

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
rewriteOnceIndexed _rs idx term =
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
          , Just subst <- [match (lhs rule) sub]
          , Just newTerm <- [replaceAt term pos (applySubstTerm subst (rhs rule))]
          ]
