{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Normalize
  ( NormalizationStatus(..)
  , normalize
  , joinableWithin
  ) where

import Data.Text (Text)
import qualified Data.Set as S
import Strat.Poly.Diagram (Diagram)
import Strat.Poly.Graph (canonicalizeDiagram)
import Strat.Poly.Rewrite (RewriteRule, rewriteOnce, rewriteAll)


data NormalizationStatus a
  = Finished a
  | OutOfFuel a
  deriving (Eq, Show)

normalize :: Int -> [RewriteRule] -> Diagram -> Either Text (NormalizationStatus Diagram)
normalize fuel rules diag
  | fuel <= 0 = do
      canon <- canonicalizeDiagram diag
      Right (OutOfFuel canon)
  | otherwise = do
      canon <- canonicalizeDiagram diag
      step <- rewriteOnce rules canon
      case step of
        Nothing -> do
          canon' <- canonicalizeDiagram diag
          Right (Finished canon')
        Just diag' -> do
          canon' <- canonicalizeDiagram diag'
          normalize (fuel - 1) rules canon'

joinableWithin :: Int -> [RewriteRule] -> Diagram -> Diagram -> Either Text Bool
joinableWithin fuel rules d1 d2
  | fuel < 0 = Right False
  | otherwise = do
      let cap = 50
      d1' <- canonicalizeDiagram d1
      d2' <- canonicalizeDiagram d2
      reach1 <- reachable rules cap fuel d1'
      reach2 <- reachable rules cap fuel d2'
      pure (not (S.null (S.intersection reach1 reach2)))

reachable :: [RewriteRule] -> Int -> Int -> Diagram -> Either Text (S.Set Diagram)
reachable rules cap fuel start =
  do
    start' <- canonicalizeDiagram start
    go (S.singleton start') [(start', 0)]
  where
    go seen [] = Right seen
    go seen ((d,depth):queue)
      | depth >= fuel = go seen queue
      | otherwise = do
          next0 <- rewriteAll cap rules d
          next <- mapM canonicalizeDiagram next0
          let new = filter (`S.notMember` seen) next
          let seen' = foldr S.insert seen new
          let queue' = queue <> [(x, depth + 1) | x <- new]
          go seen' queue'
