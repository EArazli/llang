{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.Confluence
  ( checkConfluent
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.List as L
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.Term.Normalize (normalizeTermExpr)
import Strat.Poly.Term.RewriteSystem
  ( TRS(..)
  , TRule(..)
  , applyTermSubst
  , maxBoundVarIndex
  , renameBoundVars
  , unifyTerms
  )


data CriticalPair = CriticalPair
  { cpRuleOuter :: TRule
  , cpRuleInner :: TRule
  , cpPos :: [Int]
  , cpLeft :: TermExpr
  , cpRight :: TermExpr
  }


checkConfluent :: TRS -> Either Text ()
checkConfluent trs = do
  let pairs = criticalPairs trs
  let bad =
        [ (cp, nl, nr)
        | cp <- pairs
        , let nl0 = normalizeTermExpr trs (cpLeft cp)
        , let nr0 = normalizeTermExpr trs (cpRight cp)
        , let nl = canonicalizeVars nl0
        , let nr = canonicalizeVars nr0
        , nl /= nr
        ]
  if null bad
    then Right ()
    else
      Left
        ( "confluence failed for mode "
            <> T.pack (show (trsMode trs))
            <> ": found non-joinable critical pair\n"
            <> renderBad bad
        )


criticalPairs :: TRS -> [CriticalPair]
criticalPairs trs =
  concat
    [ overlaps outer inner
    | outer <- trsRules trs
    , inner0 <- trsRules trs
    , let inner = renameRuleApart outer inner0
    ]
  where
    overlaps outer inner =
      [ CriticalPair
          { cpRuleOuter = outer
          , cpRuleInner = inner
          , cpPos = pos
          , cpLeft = replaceAt pos rhsOuter lhsInnerSub
          , cpRight = rhsInnerSub
          }
      | pos <- overlapPositions (trLHS inner)
      , not (isTrivialSelfOverlap outer inner pos)
      , Just subterm <- [subtermAt pos (trLHS inner)]
      , Just subst <- [unifyTerms (trLHS outer) subterm]
      , let lhsInnerSub = applyTermSubst subst (trLHS inner)
      , let rhsInnerSub = applyTermSubst subst (trRHS inner)
      , let rhsOuter = applyTermSubst subst (trRHS outer)
      ]

renameRuleApart :: TRule -> TRule -> TRule
renameRuleApart base rule =
  let off =
        1
          + maximum
              [ maxBoundVarIndex (trLHS base)
              , maxBoundVarIndex (trRHS base)
              ]
   in rule
        { trLHS = renameBoundVars off (trLHS rule)
        , trRHS = renameBoundVars off (trRHS rule)
        }

isTrivialSelfOverlap :: TRule -> TRule -> [Int] -> Bool
isTrivialSelfOverlap outer inner pos =
  null pos
    && trName outer == trName inner

overlapPositions :: TermExpr -> [[Int]]
overlapPositions tm =
  case tm of
    TMFun _ args -> [] : concat [ map (i :) (overlapPositions a) | (i, a) <- zip [0 :: Int ..] args ]
    _ -> []

subtermAt :: [Int] -> TermExpr -> Maybe TermExpr
subtermAt [] tm = Just tm
subtermAt (i:is) tm =
  case tm of
    TMFun _ args -> do
      arg <- nth args i
      subtermAt is arg
    _ -> Nothing

replaceAt :: [Int] -> TermExpr -> TermExpr -> TermExpr
replaceAt [] new _ = new
replaceAt (i:is) new tm =
  case tm of
    TMFun f args ->
      TMFun f (replaceNth i (replaceAt is new) args)
    _ -> tm

replaceNth :: Int -> (a -> a) -> [a] -> [a]
replaceNth _ _ [] = []
replaceNth 0 f (x:xs) = f x : xs
replaceNth i f (x:xs) = x : replaceNth (i - 1) f xs

nth :: [a] -> Int -> Maybe a
nth xs i
  | i < 0 = Nothing
  | otherwise =
      case drop i xs of
        (y:_) -> Just y
        [] -> Nothing

renderBad :: [(CriticalPair, TermExpr, TermExpr)] -> Text
renderBad bad =
  T.intercalate
    "\n"
    [ "  "
        <> renderRule (cpRuleOuter cp)
        <> " overlaps "
        <> renderRule (cpRuleInner cp)
        <> " at "
        <> T.pack (show (cpPos cp))
        <> " -> nf(left)="
        <> T.pack (show nl)
        <> ", nf(right)="
        <> T.pack (show nr)
    | (cp, nl, nr) <- L.take 10 bad
    ]

renderRule :: TRule -> Text
renderRule r = trName r

canonicalizeVars :: TermExpr -> TermExpr
canonicalizeVars tm =
  let (out, _, _) = go tm M.empty 0
   in out
  where
    go expr fwd next =
      case expr of
        TMFun fn args ->
          let (args', fwd', next') = goList args fwd next
           in (TMFun fn args', fwd', next')
        TMVar v -> (TMVar v, fwd, next)
        TMBound i ->
          case M.lookup i fwd of
            Just j -> (TMBound j, fwd, next)
            Nothing ->
              (TMBound next, M.insert i next fwd, next + 1)

    goList [] fwd next = ([], fwd, next)
    goList (x:xs) fwd next =
      let (x', fwd1, next1) = go x fwd next
          (xs', fwd2, next2) = goList xs fwd1 next1
       in (x' : xs', fwd2, next2)
