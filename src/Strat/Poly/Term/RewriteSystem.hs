{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.RewriteSystem
  ( TRule(..)
  , TRS(..)
  , TermSubst
  , mkTRS
  , rootKey
  , applyTermSubst
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
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.TypeExpr (TmFunName(..))


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
    TMFun (TmFunName f) _ -> Just (GenName f)
    _ -> Nothing

applyTermSubst :: TermSubst -> TermExpr -> TermExpr
applyTermSubst subst = go S.empty
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
        TMVar _ -> tm
        TMFun f args -> TMFun f (map (go seen) args)

renameBoundVars :: Int -> TermExpr -> TermExpr
renameBoundVars off tm =
  case tm of
    TMBound i -> TMBound (i + off)
    TMVar _ -> tm
    TMFun f args -> TMFun f (map (renameBoundVars off) args)

maxBoundVarIndex :: TermExpr -> Int
maxBoundVarIndex tm =
  case tm of
    TMBound i -> i
    TMVar _ -> -1
    TMFun _ args -> maximum (-1 : map maxBoundVarIndex args)

boundVarSet :: TermExpr -> S.Set Int
boundVarSet tm =
  case tm of
    TMBound i -> S.singleton i
    TMVar _ -> S.empty
    TMFun _ args -> S.unions (map boundVarSet args)

occursBoundVar :: Int -> TermExpr -> Bool
occursBoundVar needle tm =
  case tm of
    TMBound i -> i == needle
    TMVar _ -> False
    TMFun _ args -> any (occursBoundVar needle) args

matchPattern :: TermExpr -> TermExpr -> Maybe TermSubst
matchPattern pat tm = go M.empty pat tm
  where
    go subst patTm tgtTm =
      case patTm of
        TMBound i ->
          let tgt = applyTermSubst subst tgtTm
           in case M.lookup i subst of
                Nothing -> Just (M.insert i tgt subst)
                Just t ->
                  if t == tgt
                    then Just subst
                    else Nothing
        TMVar v ->
          case tgtTm of
            TMVar w | v == w -> Just subst
            _ -> Nothing
        TMFun f args ->
          case tgtTm of
            TMFun g args'
              | f == g
              , length args == length args' ->
                  foldM
                    (\s (a, b) -> go s a b)
                    subst
                    (zip args args')
            _ ->
              Nothing

unifyTerms :: TermExpr -> TermExpr -> Maybe TermSubst
unifyTerms lhs rhs = go M.empty [(lhs, rhs)]
  where
    go subst [] = Just subst
    go subst ((a, b):rest) =
      let a' = applyTermSubst subst a
          b' = applyTermSubst subst b
       in if a' == b'
            then go subst rest
            else
              case (a', b') of
                (TMBound i, t) -> bindVar i t subst rest
                (t, TMBound i) -> bindVar i t subst rest
                (TMFun f xs, TMFun g ys)
                  | f == g
                  , length xs == length ys ->
                      go subst (zip xs ys <> rest)
                _ -> Nothing

    bindVar i t subst rest =
      let t' = applyTermSubst subst t
       in if t' == TMBound i
            then go subst rest
            else
              if occursBoundVar i t'
                then Nothing
                else
                  let one = M.singleton i t'
                      subst' = M.insert i t' (M.map (applyTermSubst one) subst)
                      rest' = map (\(x, y) -> (applyTermSubst one x, applyTermSubst one y)) rest
                   in go subst' rest'
