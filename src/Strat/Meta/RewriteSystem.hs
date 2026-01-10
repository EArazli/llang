{-# LANGUAGE OverloadedStrings #-}
module Strat.Meta.RewriteSystem where

import Strat.Meta.Presentation
import Strat.Meta.Rule
import Strat.Meta.Types
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)

data RewriteSystem t = RewriteSystem
  { rsRules   :: [Rule t]
  , rsRuleMap :: M.Map RuleId (Rule t)
  }
  deriving (Eq, Show)

lookupRule :: RewriteSystem t -> RuleId -> Maybe (Rule t)
lookupRule rs rid = M.lookup rid (rsRuleMap rs)

getRule :: RewriteSystem t -> RuleId -> Rule t
getRule rs rid =
  case lookupRule rs rid of
    Just r  -> r
    Nothing -> error ("Rule not found: " <> show rid)

rulesInOrder :: RewriteSystem t -> [Rule t]
rulesInOrder = rsRules

-- A policy is needed because not all equations are oriented or safe for normalization
data RewritePolicy
  = UseOnlyComputationalLR
  | UseStructuralAsBidirectional
  | UseAllOriented
  deriving (Eq, Show)

compileRewriteSystem :: RewritePolicy -> Presentation t -> Either Text (RewriteSystem t)
compileRewriteSystem policy pres = do
  ensureUniqueNames (presEqs pres)
  let rules = buildRules policy (presEqs pres)
  let rulesWithIx = zipWith (\ix r -> r { ruleIx = ix }) [0 ..] rules
  let ruleMap = M.fromList [(ruleId r, r) | r <- rulesWithIx]
  pure RewriteSystem { rsRules = rulesWithIx, rsRuleMap = ruleMap }

ensureUniqueNames :: [Equation t] -> Either Text ()
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

buildRules :: RewritePolicy -> [Equation t] -> [Rule t]
buildRules policy eqs = concatMap (rulesForEq policy) eqs

rulesForEq :: RewritePolicy -> Equation t -> [Rule t]
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

mkRule :: RuleDir -> Equation t -> t -> t -> Rule t
mkRule dir eq l r =
  Rule
    { ruleId = RuleId { ridEq = eqName eq, ridDir = dir }
    , ruleIx = 0
    , ruleName = eqName eq
    , ruleClass = eqClass eq
    , lhs = l
    , rhs = r
    }
