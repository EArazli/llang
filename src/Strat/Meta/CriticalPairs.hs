{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Strat.Meta.CriticalPairs where

import Strat.Meta.Rule
import Strat.Meta.RewriteSystem
import Strat.Meta.Term.Class
import Strat.Meta.Types
import qualified Data.Map.Strict as M
import qualified Data.List as L
import Data.Text (Text)

data CriticalPair t = CriticalPair
  { cpRule1  :: RuleId
  , cpRule2  :: RuleId
  , cpPosIn2 :: Pos
  , cpPeak   :: t
  , cpLeft   :: t
  , cpRight  :: t
  , cpMgu    :: Subst t
  }

deriving instance (Eq t, Eq (Var t)) => Eq (CriticalPair t)
deriving instance (Show t, Show (Var t)) => Show (CriticalPair t)

-- Controls which overlaps matter (relative coherence)
data CPMode
  = CP_All
  | CP_OnlyStructural
  | CP_StructuralVsComputational
  deriving (Eq, Show)

criticalPairs
  :: (Unifiable t, ScopedVar (Var t))
  => CPMode
  -> (RuleId -> Rule t)
  -> RewriteSystem t
  -> Either Text [CriticalPair t]
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
      let r1' = renameRule (Ns (ruleId r1) 0) r1
          r2' = renameRule (Ns (ruleId r2) 1) r2
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
      , let peak = applySubst mgu (lhs r2')
      , let left = applySubst mgu replaced
      , let right = applySubst mgu (rhs r2')
      ]

    renameRule ns r =
      r
        { lhs = renameVars (setNs ns) (lhs r)
        , rhs = renameVars (setNs ns) (rhs r)
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
