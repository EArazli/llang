{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
module Strat.Kernel.CriticalPairs
  ( CriticalPair(..)
  , CPMode(..)
  , criticalPairs
  , criticalPairsBounded
  , criticalPairsForRules
  ) where

import Strat.Kernel.Rule
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Subst
import Strat.Kernel.Syntax (Term(..), TermNode (..), ScopeId (..), Var(..), Sort(..))
import Strat.Kernel.Term
import Strat.Kernel.Signature
import Strat.Kernel.Types
import Strat.Kernel.Unify (unify)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)

data CriticalPair = CriticalPair
  { cpRule1  :: RuleId
  , cpRule2  :: RuleId
  , cpPosIn2 :: Pos
  , cpPeak   :: Term
  , cpLeft   :: Term
  , cpRight  :: Term
  , cpMgu    :: Subst
  }

deriving instance Eq CriticalPair
deriving instance Show CriticalPair

data CPMode
  = CP_All
  | CP_OnlyStructural
  | CP_StructuralVsComputational
  deriving (Eq, Show)

criticalPairs
  :: CPMode
  -> RewriteSystem
  -> Either Text [CriticalPair]
criticalPairs mode rs =
  criticalPairsWith (rsSig rs) mode (rulesInOrder rs)

criticalPairsBounded
  :: Int
  -> CPMode
  -> RewriteSystem
  -> Either Text [CriticalPair]
criticalPairsBounded maxSize mode rs = do
  cps <- criticalPairs mode rs
  pure [cp | cp <- cps, termSize (cpPeak cp) <= maxSize]

criticalPairsForRules
  :: S.Set RuleId
  -> CPMode
  -> RewriteSystem
  -> Either Text [CriticalPair]
criticalPairsForRules allowed mode rs =
  criticalPairsWith (rsSig rs) mode (filter (\r -> ruleId r `S.member` allowed) (rulesInOrder rs))

criticalPairsWith :: Signature -> CPMode -> [Rule] -> Either Text [CriticalPair]
criticalPairsWith sig mode rules =
  Right
    [ cp
    | r1 <- rules
    , r2 <- rules
    , allowedPair mode r1 r2
    , cp <- overlaps sig r1 r2
    ]
  where
    overlaps sig' r1 r2 =
      let r1' = renameRule "0" r1
          r2' = renameRule "1" r2
      in
      [ CriticalPair
          { cpRule1 = ruleId r1
          , cpRule2 = ruleId r2
          , cpPosIn2 = pos
          , cpPeak = peak
          , cpLeft = left
          , cpRight = right
          , cpMgu = mgu
          }
      | pos <- positions (lhs r2')
      , Just sub <- [subtermAt (lhs r2') pos]
      , Just mgu <- [unify (lhs r1') sub]
      , let peak = applySubstTerm mgu (lhs r2')
      , let rhs1 = applySubstTerm mgu (rhs r1')
      , let rhs2 = applySubstTerm mgu (rhs r2')
      , Just left <- [replaceAtChecked sig' peak pos rhs1]
      , let right = rhs2
      ]

    renameRule tag r =
      let scopes = scopesInTerm (lhs r) `S.union` scopesInTerm (rhs r)
          mapping =
            M.fromList
              [ (old, ScopeId ("cp:" <> ridEq (ruleId r) <> ":" <> tag <> ":" <> renderScope old))
              | old <- S.toList scopes
              ]
      in r
          { lhs = renameScopesWith mapping (lhs r)
          , rhs = renameScopesWith mapping (rhs r)
          }

    allowedPair CP_All _ _ = True
    allowedPair CP_OnlyStructural r1 r2 =
      ruleClass r1 == Structural && ruleClass r2 == Structural
    allowedPair CP_StructuralVsComputational r1 r2 =
      (ruleClass r1 == Structural && ruleClass r2 == Computational)
        || (ruleClass r1 == Computational && ruleClass r2 == Structural)

    renameScopesWith m tm =
      Term
        { termSort = renameSort m (termSort tm)
        , termNode =
            case termNode tm of
              TVar v -> TVar (renameVar m v)
              TOp op args -> TOp op (map (renameScopesWith m) args)
        }

    renameVar m v =
      case M.lookup (vScope v) m of
        Nothing -> v
        Just new -> v { vScope = new }

    renameSort m (Sort name idx) =
      Sort name (map (renameScopesWith m) idx)

    renderScope (ScopeId t) = t

termSize :: Term -> Int
termSize tm =
  1 + case termNode tm of
    TVar _ -> 0
    TOp _ args -> sum (map termSize args)
