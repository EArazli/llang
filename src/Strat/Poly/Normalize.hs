{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Normalize
  ( NormalizationStatus(..)
  , normalize
  , joinableWithin
  , JoinWitness(..)
  , joinableWithinWitness
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Diagram (Diagram)
import Strat.Poly.Graph (CanonDiagram(..), canonDiagram, canonDiagramRaw)
import Strat.Poly.TypeTheory (TypeTheory)
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

normalize :: TypeTheory -> Int -> [RewriteRule] -> Diagram -> Either Text (NormalizationStatus Diagram)
normalize tt fuel rules diag = do
  start <- canonDiagramRaw diag
  go fuel start
  where
    go remaining current
      | remaining <= 0 =
          Right (OutOfFuel current)
      | otherwise = do
          step <- rewriteOnce tt rules current
          case step of
            Nothing ->
              Right (Finished current)
            Just next -> do
              nextCanon <- canonDiagramRaw next
              go (remaining - 1) nextCanon

joinableWithin :: TypeTheory -> Int -> [RewriteRule] -> Diagram -> Diagram -> Either Text Bool
joinableWithin tt fuel rules d1 d2
  | fuel < 0 = Right False
  | otherwise = do
      let cap = 50
      reach1 <- reachableSet tt rules cap fuel d1
      reach2 <- reachableSet tt rules cap fuel d2
      pure (not (S.null (S.intersection reach1 reach2)))

joinableWithinWitness :: TypeTheory -> Int -> [RewriteRule] -> Diagram -> Diagram -> Either Text (Maybe JoinWitness)
joinableWithinWitness tt fuel rules d1 d2
  | fuel < 0 = Right Nothing
  | otherwise = do
      let cap = 50
      nodes1 <- reachableWithParents tt rules cap fuel d1
      nodes2 <- reachableWithParents tt rules cap fuel d2
      meet <- findMeet nodes1 nodes2
      case meet of
        Nothing -> Right Nothing
        Just (i1, i2) -> do
          let path1 = pathFrom nodes1 i1
          let path2 = pathFrom nodes2 i2
          let meetDiag = nodeDiag (nodes1 !! i1)
          Right (Just JoinWitness { jwMeet = meetDiag, jwLeft = path1, jwRight = path2 })

data Node = Node
  { nodeCanon :: CanonDiagram
  , nodeParent :: Maybe Int
  , nodeDepth :: Int
  } deriving (Eq, Show)

nodeDiag :: Node -> Diagram
nodeDiag = unCanon . nodeCanon

reachableWithParents :: TypeTheory -> [RewriteRule] -> Int -> Int -> Diagram -> Either Text [Node]
reachableWithParents tt rules cap fuel start = do
  startCanon <- canonDiagram start
  let startNode = Node startCanon Nothing 0
  go [startNode] (M.singleton startCanon 0) [0]
  where
    go nodes _ [] = Right nodes
    go nodes seen (idx:rest) =
      case indexMaybe nodes idx of
        Nothing -> Right nodes
        Just node ->
          if nodeDepth node >= fuel
            then go nodes seen rest
            else do
              next0 <- rewriteAll tt cap rules (nodeDiag node)
              next <- mapM canonDiagram next0
              (nodes', seen', newIdxs) <- foldl (insertIfNew idx (nodeDepth node + 1)) (Right (nodes, seen, [])) next
              go nodes' seen' (rest <> newIdxs)

    insertIfNew parent depth acc canon = do
      (nodes, seen, newIdxs) <- acc
      case M.lookup canon seen of
        Just _ ->
          Right (nodes, seen, newIdxs)
        Nothing -> do
          let idx = length nodes
          let node = Node canon (Just parent) depth
          Right (nodes <> [node], M.insert canon idx seen, newIdxs <> [idx])

findMeet :: [Node] -> [Node] -> Either Text (Maybe (Int, Int))
findMeet nodes1 nodes2 = go 0
  where
    ix2 = M.fromList [ (nodeCanon n, i) | (i, n) <- zip [0 :: Int ..] nodes2 ]

    go i =
          if i >= length nodes1
            then Right Nothing
            else
              case M.lookup (nodeCanon (nodes1 !! i)) ix2 of
                Nothing -> go (i + 1)
                Just j -> Right (Just (i, j))

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

reachableSet :: TypeTheory -> [RewriteRule] -> Int -> Int -> Diagram -> Either Text (S.Set CanonDiagram)
reachableSet tt rules cap fuel start = do
  startCanon <- canonDiagram start
  go (S.singleton startCanon) [(startCanon, 0)]
  where
    go seen [] = Right seen
    go seen ((diag, depth):queue)
      | depth >= fuel = go seen queue
      | otherwise = do
          next0 <- rewriteAll tt cap rules (unCanon diag)
          next <- mapM canonDiagram next0
          let nextSet = S.fromList next
          let unseen = S.difference nextSet seen
          let seen' = S.union seen unseen
          let queue' =
                queue
                  <> [ (c, depth + 1)
                     | c <- next
                     , c `S.member` unseen
                     ]
          go seen' queue'

indexMaybe :: [a] -> Int -> Maybe a
indexMaybe xs i
  | i < 0 = Nothing
  | otherwise =
      case drop i xs of
        (y:_) -> Just y
        [] -> Nothing
