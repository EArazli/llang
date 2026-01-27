{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Normalize
  ( NormalizationStatus(..)
  , normalize
  , joinableWithin
  ) where

import Data.Text (Text)
import Strat.Poly.Diagram (Diagram)
import Strat.Poly.Graph (renumberDiagram, diagramIsoEq)
import Strat.Poly.Rewrite (RewriteRule, rewriteOnce, rewriteAll)


data NormalizationStatus a
  = Finished a
  | OutOfFuel a
  deriving (Eq, Show)

normalize :: Int -> [RewriteRule] -> Diagram -> Either Text (NormalizationStatus Diagram)
normalize fuel rules diag
  | fuel <= 0 = do
      canon <- renumberDiagram diag
      Right (OutOfFuel canon)
  | otherwise = do
      canon <- renumberDiagram diag
      step <- rewriteOnce rules canon
      case step of
        Nothing -> do
          canon' <- renumberDiagram diag
          Right (Finished canon')
        Just diag' -> do
          canon' <- renumberDiagram diag'
          normalize (fuel - 1) rules canon'

joinableWithin :: Int -> [RewriteRule] -> Diagram -> Diagram -> Either Text Bool
joinableWithin fuel rules d1 d2
  | fuel < 0 = Right False
  | otherwise = do
      let cap = 50
      d1' <- renumberDiagram d1
      d2' <- renumberDiagram d2
      reach1 <- reachable rules cap fuel d1'
      reach2 <- reachable rules cap fuel d2'
      anyIso reach1 reach2

reachable :: [RewriteRule] -> Int -> Int -> Diagram -> Either Text [Diagram]
reachable rules cap fuel start =
  do
    start' <- renumberDiagram start
    go [start'] [(start', 0)]
  where
    go seen [] = Right seen
    go seen ((d,depth):queue)
      | depth >= fuel = go seen queue
      | otherwise = do
          next0 <- rewriteAll cap rules d
          next <- mapM renumberDiagram next0
          (seen', new) <- foldl insertIfNew (Right (seen, [])) next
          let queue' = queue <> [(x, depth + 1) | x <- new]
          go seen' queue'
    insertIfNew acc diag = do
      (seenAcc, newAcc) <- acc
      present <- isIsoMember diag seenAcc
      if present
        then Right (seenAcc, newAcc)
        else Right (seenAcc <> [diag], newAcc <> [diag])

anyIso :: [Diagram] -> [Diagram] -> Either Text Bool
anyIso [] _ = Right False
anyIso (x:xs) ys = do
  hit <- isIsoMember x ys
  if hit then Right True else anyIso xs ys

isIsoMember :: Diagram -> [Diagram] -> Either Text Bool
isIsoMember _ [] = Right False
isIsoMember d (x:xs) = do
  eq <- diagramIsoEq d x
  if eq then Right True else isIsoMember d xs
