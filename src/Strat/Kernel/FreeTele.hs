{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.FreeTele
  ( freeTeleOfTerm
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Kernel.Syntax (Binder(..), Sort(..), Term(..), TermNode(..), Var)


freeTeleOfTerm :: Term -> Either Text [Binder]
freeTeleOfTerm term = do
  vars <- collectTerm term M.empty
  ordered <- topoOrder vars
  pure [Binder v s | v <- ordered, Just s <- [M.lookup v vars]]

collectTerm :: Term -> M.Map Var Sort -> Either Text (M.Map Var Sort)
collectTerm t acc = do
  acc' <- collectSort (termSort t) acc
  case termNode t of
    TVar v -> insertVar v (termSort t) acc'
    TOp _ args -> foldlM (flip collectTerm) acc' args

collectSort :: Sort -> M.Map Var Sort -> Either Text (M.Map Var Sort)
collectSort (Sort _ idxTerms) acc =
  foldlM (flip collectTerm) acc idxTerms

insertVar :: Var -> Sort -> M.Map Var Sort -> Either Text (M.Map Var Sort)
insertVar v s acc =
  case M.lookup v acc of
    Nothing -> Right (M.insert v s acc)
    Just s'
      | s' == s -> Right acc
      | otherwise -> Left "freeTeleOfTerm: variable sort mismatch"

varsInSort :: Sort -> S.Set Var
varsInSort (Sort _ idxTerms) = S.unions (map varsInTerm idxTerms)

varsInTerm :: Term -> S.Set Var
varsInTerm t =
  varsInSort (termSort t) `S.union`
    case termNode t of
      TVar v -> S.singleton v
      TOp _ args -> S.unions (map varsInTerm args)

topoOrder :: M.Map Var Sort -> Either Text [Var]
topoOrder vars =
  let deps = M.map (S.filter (`M.member` vars) . varsInSort) vars
      rev = buildReverse deps
      indeg = M.map S.size deps
      zero = S.fromList [ v | (v, d) <- M.toList indeg, d == 0 ]
  in go indeg rev zero []
  where
    buildReverse m =
      M.fromListWith S.union
        [ (dep, S.singleton v)
        | (v, ds) <- M.toList m
        , dep <- S.toList ds
        ]

    go indeg rev zero acc
      | S.null zero =
          if length acc == M.size vars
            then Right (reverse acc)
            else Left "freeTeleOfTerm: cyclic sort dependency"
      | otherwise =
          let v = S.findMin zero
              zero' = S.delete v zero
              dependents = M.findWithDefault S.empty v rev
          in case foldlM (updateInDegree v) (indeg, zero') (S.toList dependents) of
              Left err -> Left err
              Right (indeg', zero'') -> go indeg' rev zero'' (v : acc)

    updateInDegree _ (indeg, zero) node =
      case M.lookup node indeg of
        Nothing -> Right (indeg, zero)
        Just n ->
          let n' = n - 1
              indeg' = M.insert node n' indeg
              zero' = if n' == 0 then S.insert node zero else zero
          in Right (indeg', zero')

foldlM :: (a -> b -> Either Text a) -> a -> [b] -> Either Text a
foldlM _ acc [] = Right acc
foldlM f acc (x:xs) = do
  acc' <- f acc x
  foldlM f acc' xs
