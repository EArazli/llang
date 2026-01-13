{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.RewriteSystem
  ( RewriteSystem(..)
  , lookupRule
  , getRule
  , rulesInOrder
  , RewritePolicy(..)
  , compileRewriteSystem
  ) where

import Strat.Kernel.Presentation
import Strat.Kernel.Rule
import Strat.Kernel.Syntax
import Strat.Kernel.Types
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)

data RewriteSystem = RewriteSystem
  { rsRules   :: [Rule]
  , rsRuleMap :: M.Map RuleId Rule
  }
  deriving (Eq, Show)

lookupRule :: RewriteSystem -> RuleId -> Maybe Rule
lookupRule rs rid = M.lookup rid (rsRuleMap rs)

getRule :: RewriteSystem -> RuleId -> Rule
getRule rs rid =
  case lookupRule rs rid of
    Just r  -> r
    Nothing -> error ("Rule not found: " <> show rid)

rulesInOrder :: RewriteSystem -> [Rule]
rulesInOrder = rsRules

-- A policy is needed because not all equations are oriented or safe for normalization
data RewritePolicy
  = UseOnlyComputationalLR
  | UseStructuralAsBidirectional
  | UseAllOriented
  deriving (Eq, Show)

compileRewriteSystem :: RewritePolicy -> Presentation -> Either Text RewriteSystem
compileRewriteSystem policy pres = do
  validatePresentation pres
  ensureUniqueNames (presEqs pres)
  let rules = buildRules policy (presEqs pres)
  let rulesWithIx = zipWith (\ix r -> r { ruleIx = ix }) [0 ..] rules
  let ruleMap = M.fromList [(ruleId r, r) | r <- rulesWithIx]
  pure RewriteSystem { rsRules = rulesWithIx, rsRuleMap = ruleMap }

ensureUniqueNames :: [Equation] -> Either Text ()
ensureUniqueNames eqs =
  case findDuplicate (map eqName eqs) of
    Nothing -> Right ()
    Just dup -> Left ("Duplicate equation name: " <> dup)
  where
    findDuplicate names = go S.empty names
    go _ [] = Nothing
    go seen (n : ns)
      | n `S.member` seen = Just n
      | otherwise = go (S.insert n seen) ns

buildRules :: RewritePolicy -> [Equation] -> [Rule]
buildRules policy eqs = concatMap (rulesForEq policy) eqs

rulesForEq :: RewritePolicy -> Equation -> [Rule]
rulesForEq policy eq =
  case policy of
    UseStructuralAsBidirectional ->
      case eqClass eq of
        Structural ->
          [ mkRule DirLR eq (eqLHS eq) (eqRHS eq)
          , mkRule DirRL eq (eqRHS eq) (eqLHS eq)
          ]
        Computational ->
          rulesFromOrientation (eqOrient eq)
    UseOnlyComputationalLR ->
      case eqClass eq of
        Computational ->
          case eqOrient eq of
            LR -> [mkRule DirLR eq (eqLHS eq) (eqRHS eq)]
            Bidirectional -> [mkRule DirLR eq (eqLHS eq) (eqRHS eq)]
            _ -> []
        Structural -> []
    UseAllOriented ->
      rulesFromOrientation (eqOrient eq)
  where
    rulesFromOrientation orient =
      case orient of
        LR -> [mkRule DirLR eq (eqLHS eq) (eqRHS eq)]
        RL -> [mkRule DirRL eq (eqRHS eq) (eqLHS eq)]
        Bidirectional ->
          [ mkRule DirLR eq (eqLHS eq) (eqRHS eq)
          , mkRule DirRL eq (eqRHS eq) (eqLHS eq)
          ]
        Unoriented -> []

mkRule :: RuleDir -> Equation -> Term -> Term -> Rule
mkRule dir eq l r =
  Rule
    { ruleId = RuleId { ridEq = eqName eq, ridDir = dir }
    , ruleIx = 0
    , ruleName = eqName eq
    , ruleClass = eqClass eq
    , lhs = l
    , rhs = r
    }
