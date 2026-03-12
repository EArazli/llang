{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.RewriteSystem
  ( TRule(..)
  , TRS(..)
  , TermSubst
  , mkTRS
  , rootKey
  , applyTermSubstClosed
  , applyTermSubstOnce
  , renameBoundVars
  , maxBoundVarIndex
  , boundVarSet
  , occursBoundVar
  , matchPattern
  , unifyTerms
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeSyntax (ModeName)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Term.AST (TermExpr(..), TermHeadArg(..))


data TRule = TRule
  { trName :: Text
  , trLHS  :: TermExpr
  , trRHS  :: TermExpr
  } deriving (Eq, Ord, Show)

data TRS = TRS
  { trsMode  :: ModeName
  , trsRules :: [TRule]
  , trsIndex :: M.Map (Maybe GenName) [TRule]
  } deriving (Eq, Ord, Show)

type TermSubst = M.Map Int TermExpr

mkTRS :: ModeName -> [TRule] -> TRS
mkTRS mode rules =
  TRS
    { trsMode = mode
    , trsRules = rules
    , trsIndex = foldl insertRule M.empty rules
    }
  where
    insertRule mp rule =
      M.insertWith (<>) (rootKey (trLHS rule)) [rule] mp

rootKey :: TermExpr -> Maybe GenName
rootKey tm =
  case tm of
    TMGen f _ -> Just f
    _ -> Nothing

applyTermSubstClosed :: TermSubst -> TermExpr -> TermExpr
applyTermSubstClosed subst = go S.empty
  where
    go seen tm =
      case tm of
        TMBound i ->
          case M.lookup i subst of
            Nothing -> TMBound i
            Just t ->
              if i `S.member` seen
                then TMBound i
                else go (S.insert i seen) t
        TMMeta _ _ -> tm
        TMGen f args -> TMGen f (map (mapHeadArg (go seen)) args)
        TMLit lit -> TMLit lit

applyTermSubstOnce :: TermSubst -> TermExpr -> TermExpr
applyTermSubstOnce subst = go
  where
    go tm =
      case tm of
        TMBound i ->
          case M.lookup i subst of
            Nothing -> TMBound i
            Just t -> t
        TMMeta _ _ -> tm
        TMGen f args -> TMGen f (map (mapHeadArg go) args)
        TMLit lit -> TMLit lit

renameBoundVars :: Int -> TermExpr -> TermExpr
renameBoundVars off tm =
  case tm of
    TMBound i -> TMBound (i + off)
    TMMeta v args -> TMMeta v (map (+ off) args)
    TMGen f args -> TMGen f (map (mapHeadArg (renameBoundVars off)) args)
    TMLit lit -> TMLit lit

maxBoundVarIndex :: TermExpr -> Int
maxBoundVarIndex tm =
  case tm of
    TMBound i -> i
    TMMeta _ args -> maximum (-1 : args)
    TMGen _ args -> maximum (-1 : map maxHeadArg args)
    TMLit _ -> -1
  where
    maxHeadArg arg =
      case arg of
        THAObj _ -> -1
        THATm inner -> maxBoundVarIndex inner

boundVarSet :: TermExpr -> S.Set Int
boundVarSet tm =
  case tm of
    TMBound i -> S.singleton i
    TMMeta _ args -> S.fromList args
    TMGen _ args -> S.unions (map boundHeadArg args)
    TMLit _ -> S.empty
  where
    boundHeadArg arg =
      case arg of
        THAObj _ -> S.empty
        THATm inner -> boundVarSet inner

occursBoundVar :: Int -> TermExpr -> Bool
occursBoundVar needle tm =
  case tm of
    TMBound i -> i == needle
    TMMeta _ args -> needle `elem` args
    TMGen _ args -> any occursHeadArg args
    TMLit _ -> False
  where
    occursHeadArg arg =
      case arg of
        THAObj _ -> False
        THATm inner -> occursBoundVar needle inner

matchPattern :: TermExpr -> TermExpr -> Maybe TermSubst
matchPattern pat tm = go M.empty pat tm
  where
    go subst patTm tgtTm =
      case patTm of
        TMBound i ->
          let tgt = tgtTm
           in case M.lookup i subst of
                Nothing -> Just (M.insert i tgt subst)
                Just t ->
                  if t == tgt
                    then Just subst
                    else Nothing
        TMMeta v args ->
          case tgtTm of
            TMMeta w args' | v == w && args == args' -> Just subst
            _ -> Nothing
        TMGen f args ->
          case tgtTm of
            TMGen g args'
              | f == g
              , length args == length args' ->
                  foldM
                    (\s (a, b) -> matchHeadArg s a b)
                    subst
                    (zip args args')
            _ ->
              Nothing
        TMLit lit ->
          case tgtTm of
            TMLit lit' | lit == lit' -> Just subst
            _ -> Nothing
    matchHeadArg subst argA argB =
      case (argA, argB) of
        (THAObj objA, THAObj objB)
          | objA == objB -> Just subst
          | otherwise -> Nothing
        (THATm tmA, THATm tmB) -> go subst tmA tmB
        _ -> Nothing

unifyTerms :: TermExpr -> TermExpr -> Maybe TermSubst
unifyTerms lhs rhs = go M.empty [(lhs, rhs)]
  where
    go subst [] = Just subst
    go subst ((a, b):rest) =
      let a' = applyTermSubstClosed subst a
          b' = applyTermSubstClosed subst b
       in if a' == b'
            then go subst rest
            else
              case (a', b') of
                (TMBound i, t) -> bindVar i t subst rest
                (t, TMBound i) -> bindVar i t subst rest
                (TMGen f xs, TMGen g ys)
                  | f == g
                  , length xs == length ys ->
                      case zipHeadArgs xs ys of
                        Nothing -> Nothing
                        Just pairs -> go subst (pairs <> rest)
                (TMMeta v args, TMMeta w args')
                  | v == w
                  , args == args' ->
                      go subst rest
                _ -> Nothing

    bindVar i t subst rest =
      let t' = applyTermSubstClosed subst t
       in if t' == TMBound i
            then go subst rest
            else
              if occursBoundVar i t'
                then Nothing
                else
                  let one = M.singleton i t'
                      subst' = M.insert i t' (M.map (applyTermSubstClosed one) subst)
                      rest' = map (\(x, y) -> (applyTermSubstClosed one x, applyTermSubstClosed one y)) rest
                   in go subst' rest'

mapHeadArg :: (TermExpr -> TermExpr) -> TermHeadArg -> TermHeadArg
mapHeadArg f arg =
  case arg of
    THAObj obj -> THAObj obj
    THATm tm -> THATm (f tm)

zipHeadArgs :: [TermHeadArg] -> [TermHeadArg] -> Maybe [(TermExpr, TermExpr)]
zipHeadArgs [] [] = Just []
zipHeadArgs (THATm a : as) (THATm b : bs) = ((a, b) :) <$> zipHeadArgs as bs
zipHeadArgs (THAObj objA : as) (THAObj objB : bs)
  | objA == objB = zipHeadArgs as bs
  | otherwise = Nothing
zipHeadArgs _ _ = Nothing
