{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Normalize
  ( NormalizationStatus(..)
  , normalize
  , joinableWithin
  , JoinWitness(..)
  , joinableWithinWitness
  ) where

import Data.Text (Text)
import Strat.Poly.Diagram (Diagram)
import Strat.Poly.Graph (renumberDiagram, diagramIsoEq)
import Strat.Poly.ModeTheory (ModeTheory)
import Strat.Poly.Rewrite (RewriteRule, rewriteOnce, rewriteAll)


data NormalizationStatus a
  = Finished a
  | OutOfFuel a
  deriving (Eq, Show)

data JoinWitness = JoinWitness
  { jwMeet  :: Diagram
  , jwLeft  :: [Diagram]
  , jwRight :: [Diagram]
  } deriving (Eq, Show)

normalize :: ModeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text (NormalizationStatus Diagram)
normalize mt fuel rules diag
  | fuel <= 0 = do
      canon <- renumberDiagram diag
      Right (OutOfFuel canon)
  | otherwise = do
      canon <- renumberDiagram diag
      step <- rewriteOnce mt rules canon
      case step of
        Nothing -> do
          canon' <- renumberDiagram diag
          Right (Finished canon')
        Just diag' -> do
          canon' <- renumberDiagram diag'
          normalize mt (fuel - 1) rules canon'

joinableWithin :: ModeTheory -> Int -> [RewriteRule] -> Diagram -> Diagram -> Either Text Bool
joinableWithin mt fuel rules d1 d2
  | fuel < 0 = Right False
  | otherwise = do
      let cap = 50
      d1' <- renumberDiagram d1
      d2' <- renumberDiagram d2
      reach1 <- reachable mt rules cap fuel d1'
      reach2 <- reachable mt rules cap fuel d2'
      anyIso reach1 reach2

joinableWithinWitness :: ModeTheory -> Int -> [RewriteRule] -> Diagram -> Diagram -> Either Text (Maybe JoinWitness)
joinableWithinWitness mt fuel rules d1 d2
  | fuel < 0 = Right Nothing
  | otherwise = do
      let cap = 50
      nodes1 <- reachableWithParents mt rules cap fuel d1
      nodes2 <- reachableWithParents mt rules cap fuel d2
      meet <- findMeet nodes1 nodes2
      case meet of
        Nothing -> Right Nothing
        Just (i1, i2) -> do
          let path1 = pathFrom nodes1 i1
          let path2 = pathFrom nodes2 i2
          let meetDiag = nodeDiag (nodes1 !! i1)
          Right (Just JoinWitness { jwMeet = meetDiag, jwLeft = path1, jwRight = path2 })

data Node = Node
  { nodeDiag :: Diagram
  , nodeParent :: Maybe Int
  , nodeDepth :: Int
  } deriving (Eq, Show)

reachableWithParents :: ModeTheory -> [RewriteRule] -> Int -> Int -> Diagram -> Either Text [Node]
reachableWithParents mt rules cap fuel start = do
  start' <- renumberDiagram start
  go [Node start' Nothing 0] [0]
  where
    go nodes [] = Right nodes
    go nodes (idx:rest) =
      case indexMaybe nodes idx of
        Nothing -> Right nodes
        Just node ->
          if nodeDepth node >= fuel
            then go nodes rest
            else do
              next0 <- rewriteAll mt cap rules (nodeDiag node)
              next <- mapM renumberDiagram next0
              (nodes', newIdxs) <- foldl (insertIfNew idx (nodeDepth node + 1)) (Right (nodes, [])) next
              go nodes' (rest <> newIdxs)

    insertIfNew parent depth acc diag = do
      (nodes, newIdxs) <- acc
      present <- isIsoNode diag nodes
      if present
        then Right (nodes, newIdxs)
        else do
          let idx = length nodes
          Right (nodes <> [Node diag (Just parent) depth], newIdxs <> [idx])

isIsoNode :: Diagram -> [Node] -> Either Text Bool
isIsoNode _ [] = Right False
isIsoNode d (n:ns) = do
  eq <- isoEqOrFalse d (nodeDiag n)
  if eq then Right True else isIsoNode d ns

findMeet :: [Node] -> [Node] -> Either Text (Maybe (Int, Int))
findMeet nodes1 nodes2 = go 0
  where
    go i =
      if i >= length nodes1
        then Right Nothing
        else do
          let d1 = nodeDiag (nodes1 !! i)
          j <- findIsoIndex d1 nodes2 0
          case j of
            Nothing -> go (i + 1)
            Just idx -> Right (Just (i, idx))

    findIsoIndex _ [] _ = Right Nothing
    findIsoIndex d (n:ns) j = do
      eq <- isoEqOrFalse d (nodeDiag n)
      if eq then Right (Just j) else findIsoIndex d ns (j + 1)

pathFrom :: [Node] -> Int -> [Diagram]
pathFrom nodes idx = go idx []
  where
    go i acc =
      case indexMaybe nodes i of
        Nothing -> acc
        Just node ->
          let acc' = nodeDiag node : acc
          in case nodeParent node of
            Nothing -> acc'
            Just p -> go p acc'

indexMaybe :: [a] -> Int -> Maybe a
indexMaybe xs i
  | i < 0 = Nothing
  | otherwise =
      case drop i xs of
        (y:_) -> Just y
        [] -> Nothing

reachable :: ModeTheory -> [RewriteRule] -> Int -> Int -> Diagram -> Either Text [Diagram]
reachable mt rules cap fuel start =
  do
    start' <- renumberDiagram start
    go [start'] [(start', 0)]
  where
    go seen [] = Right seen
    go seen ((d,depth):queue)
      | depth >= fuel = go seen queue
      | otherwise = do
          next0 <- rewriteAll mt cap rules d
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
  eq <- isoEqOrFalse d x
  if eq then Right True else isIsoMember d xs

isoEqOrFalse :: Diagram -> Diagram -> Either Text Bool
isoEqOrFalse a b =
  case diagramIsoEq a b of
    Left _ -> Right False
    Right ok -> Right ok
