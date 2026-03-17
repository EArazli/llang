{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.Confluence
  ( checkConfluent
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.List as L
import Strat.Poly.Term.AST (TermExpr(..), TermHeadArg(..))
import Strat.Poly.Term.Normalize (normalizeTermExpr)
import Strat.Poly.Term.RewriteSystem
  ( TRS(..)
  , TRule(..)
  , applyTermSubstClosed
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
      , Just rhsInner0 <- [trRHS inner]
      , Just rhsOuter0 <- [trRHS outer]
      , let lhsInnerSub = applyTermSubstClosed subst (trLHS inner)
      , let rhsInnerSub = applyTermSubstClosed subst rhsInner0
      , let rhsOuter = applyTermSubstClosed subst rhsOuter0
      ]

renameRuleApart :: TRule -> TRule -> TRule
renameRuleApart base rule =
  let off =
        1
          + maximum
              [ maxBoundVarIndex (trLHS base)
              , maybe (-1) maxBoundVarIndex (trRHS base)
              ]
   in rule
        { trLHS = renameBoundVars off (trLHS rule)
        , trRHS = renameBoundVars off <$> trRHS rule
        }

isTrivialSelfOverlap :: TRule -> TRule -> [Int] -> Bool
isTrivialSelfOverlap outer inner pos =
  null pos
    && trName outer == trName inner

overlapPositions :: TermExpr -> [[Int]]
overlapPositions tm =
  case tm of
    TMHead _ args _ ->
      [] : concat [ map (i :) (overlapArgPositions a) | (i, a) <- zip [0 :: Int ..] args ]
    _ -> []

overlapArgPositions :: TermHeadArg -> [[Int]]
overlapArgPositions arg =
  case arg of
    THAObj _ -> []
    THATm tm -> overlapPositions tm

subtermAt :: [Int] -> TermExpr -> Maybe TermExpr
subtermAt [] tm = Just tm
subtermAt (i:is) tm =
  case tm of
    TMHead _ args _ -> do
      arg <- nth args i
      subtermAtArg is arg
    _ -> Nothing

subtermAtArg :: [Int] -> TermHeadArg -> Maybe TermExpr
subtermAtArg _ (THAObj _) = Nothing
subtermAtArg is (THATm tm) = subtermAt is tm

replaceAt :: [Int] -> TermExpr -> TermExpr -> TermExpr
replaceAt [] new _ = new
replaceAt (i:is) new tm =
  case tm of
    TMHead f args bargs ->
      TMHead f (replaceNth i (replaceHeadArgAt is new) args) bargs
    _ -> tm

replaceHeadArgAt :: [Int] -> TermExpr -> TermHeadArg -> TermHeadArg
replaceHeadArgAt _ _ arg@(THAObj _) = arg
replaceHeadArgAt is new (THATm tm) = THATm (replaceAt is new tm)

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
        TMHead fn args bargs ->
          let (args', fwd', next') = goHeadArgs args fwd next
           in (TMHead fn args' bargs, fwd', next')
        TMSplice hole me args ->
          let (args', fwd', next') = goArgs args fwd next
           in (TMSplice hole me args', fwd', next')
        TMMeta v args ->
          let (args', fwd', next') = renameArgs args fwd next
           in (TMMeta v args', fwd', next')
        TMBound i ->
          case M.lookup i fwd of
            Just j -> (TMBound j, fwd, next)
            Nothing ->
              (TMBound next, M.insert i next fwd, next + 1)
        TMLit lit -> (TMLit lit, fwd, next)

    goHeadArgs [] fwd next = ([], fwd, next)
    goHeadArgs (x:xs) fwd next =
      let (x', fwd1, next1) = goHeadArg x fwd next
          (xs', fwd2, next2) = goHeadArgs xs fwd1 next1
       in (x' : xs', fwd2, next2)

    goHeadArg arg fwd next =
      case arg of
        THAObj obj -> (THAObj obj, fwd, next)
        THATm tm0 ->
          let (tm1, fwd1, next1) = go tm0 fwd next
           in (THATm tm1, fwd1, next1)

    goArgs [] fwd next = ([], fwd, next)
    goArgs (x:xs) fwd next =
      let (x', fwd1, next1) = go x fwd next
          (xs', fwd2, next2) = goArgs xs fwd1 next1
       in (x' : xs', fwd2, next2)

    renameArgs [] fwd next = ([], fwd, next)
    renameArgs (i:is) fwd next =
      let (j, fwd1, next1) =
            case M.lookup i fwd of
              Just k -> (k, fwd, next)
              Nothing -> (next, M.insert i next fwd, next + 1)
          (is', fwd2, next2) = renameArgs is fwd1 next1
       in (j : is', fwd2, next2)
