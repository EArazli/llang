{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
module Strat.Kernel.CriticalPairs where

import Strat.Kernel.Rule
import Strat.Kernel.RewriteSystem
import Strat.Kernel.Subst
import Strat.Kernel.Syntax (Term, ScopeId (..))
import Strat.Kernel.Term
import Strat.Kernel.Types
import Strat.Kernel.Unify (unify)
import qualified Data.List as L
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
  -> (RuleId -> Rule)
  -> RewriteSystem
  -> Either Text [CriticalPair]
criticalPairs mode _lookup rs = do
  case firstNonLinear of
    Just rid -> Left ("Non-left-linear rule in criticalPairs: " <> rid)
    Nothing ->
      Right
        [ cp
        | r1 <- rulesInOrder rs
        , r2 <- rulesInOrder rs
        , allowedPair mode r1 r2
        , cp <- overlaps r1 r2
        ]
  where
    firstNonLinear =
      case L.find (not . isLeftLinear . lhs) (rulesInOrder rs) of
        Nothing -> Nothing
        Just r -> Just (ridEq (ruleId r))

    overlaps r1 r2 =
      let r1' = renameRule (ScopeId ("cp:" <> ridEq (ruleId r1) <> ":0")) r1
          r2' = renameRule (ScopeId ("cp:" <> ridEq (ruleId r2) <> ":1")) r2
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
      , not (isVar sub)
      , Just mgu <- [unify (lhs r1') sub]
      , Just replaced <- [replaceAt (lhs r2') pos (rhs r1')]
      , let peak = applySubstTerm mgu (lhs r2')
      , let left = applySubstTerm mgu replaced
      , let right = applySubstTerm mgu (rhs r2')
      ]

    renameRule scope r =
      let renameAll t =
            foldl
              (\acc old -> renameScope old scope acc)
              t
              (S.toList (scopesInTerm t))
      in r
          { lhs = renameAll (lhs r)
          , rhs = renameAll (rhs r)
          }

    allowedPair CP_All _ _ = True
    allowedPair CP_OnlyStructural r1 r2 =
      ruleClass r1 == Structural && ruleClass r2 == Structural
    allowedPair CP_StructuralVsComputational r1 r2 =
      (ruleClass r1 == Structural && ruleClass r2 == Computational)
        || (ruleClass r1 == Computational && ruleClass r2 == Structural)

    isLeftLinear term =
      all (<= 1) (M.elems counts)
      where
        counts = foldl countVar M.empty (positions term)
        countVar m pos =
          case subtermAt term pos >>= asVar of
            Nothing -> m
            Just v -> M.insertWith (+) v 1 m
