{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.CartLib
  ( dropCtx
  , swapAdjacent
  , bubbleLeftTo0
  , projWire
  , dupCtx
  , pairArgs
  ) where

import Data.Text (Text)
import Data.List (findIndex)
import Strat.Poly.Diagram
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.TypeExpr (Context, TypeExpr)


dropCtx :: ModeName -> Context -> Diagram
dropCtx mode [] = idD mode []
dropCtx mode (a : rest) =
  DTensor (genD mode [a] [] (GLDrop a)) (dropCtx mode rest)

swapAdjacent :: ModeName -> Context -> Int -> Either Text Diagram
swapAdjacent mode ctx i
  | i < 0 || i + 1 >= length ctx = Left "swapAdjacent: index out of bounds"
  | otherwise =
      case drop i ctx of
        (a : b : suffix) -> do
          let prefix = take i ctx
          left <- tensorD (idD mode prefix) (genD mode [a, b] [b, a] (GLSwap a b))
          tensorD left (idD mode suffix)
        _ -> Left "swapAdjacent: index out of bounds"

bubbleLeftTo0 :: ModeName -> Context -> Int -> Either Text (Diagram, Context)
bubbleLeftTo0 mode ctx i
  | i < 0 || i >= length ctx = Left "bubbleLeftTo0: index out of bounds"
  | i == 0 = Right (idD mode ctx, ctx)
  | otherwise = do
      swap <- swapAdjacent mode ctx (i - 1)
      let ctx' = swapAt (i - 1) ctx
      (rest, finalCtx) <- bubbleLeftTo0 mode ctx' (i - 1)
      composed <- compD rest swap
      Right (composed, finalCtx)

projWire :: ModeName -> Context -> Int -> Either Text Diagram
projWire mode ctx i = do
  (bubble, ctx') <- bubbleLeftTo0 mode ctx i
  case ctx' of
    [] -> Left "projWire: empty context"
    (a : rest) -> do
      proj <- tensorD (idD mode [a]) (dropCtx mode rest)
      compD proj bubble


data WireTag = WireTag
  { wtIndex :: Int
  , wtCopy :: Int
  , wtType :: TypeExpr
  }
  deriving (Eq, Show)


dupCtx :: ModeName -> Context -> Either Text Diagram
dupCtx mode ctx = do
  dupBase <- dupBaseCtx mode ctx
  shuffle <- shuffleDup mode ctx
  compD shuffle dupBase

pairArgs :: ModeName -> Context -> [Diagram] -> Either Text Diagram
pairArgs mode ctx [] = Right (dropCtx mode ctx)
pairArgs _ _ [d] = Right d
pairArgs mode ctx (d : ds)
  | any ((/= ctx) . diagramDom) (d : ds) = Left "pairArgs: domain mismatch"
  | otherwise = do
      rest <- pairArgs mode ctx ds
      dup <- dupCtx mode ctx
      tens <- tensorD d rest
      compD tens dup


swapAt :: Int -> [a] -> [a]
swapAt i xs =
  let (prefix, rest) = splitAt i xs
  in case rest of
      (a : b : suffix) -> prefix <> [b, a] <> suffix
      _ -> xs


dupBaseCtx :: ModeName -> Context -> Either Text Diagram
dupBaseCtx mode [] = Right (idD mode [])
dupBaseCtx mode (a : rest) = do
  restDiag <- dupBaseCtx mode rest
  tensorD (genD mode [a] [a, a] (GLDup a)) restDiag


shuffleDup :: ModeName -> Context -> Either Text Diagram
shuffleDup mode ctx = do
  let n = length ctx
  let ctxDup = concatMap (\a -> [a, a]) ctx
  let tags = concatMap (\(ix, a) -> [WireTag ix 0 a, WireTag ix 1 a]) (zip [0 ..] ctx)
  go n ctxDup tags (idD mode ctxDup)
  where
    go n currentCtx currentTags acc
      | n <= 0 = Right acc
      | otherwise = do
          let ix = n - 1
          pos <- findTagPos ix currentTags
          let target = length ctx + ix
          (acc', ctx', tags') <- bubbleRight currentCtx currentTags acc pos target
          go ix ctx' tags' acc'

    findTagPos ix tags =
      case findIndex (\t -> wtIndex t == ix && wtCopy t == 1) tags of
        Nothing -> Left "shuffleDup: missing tagged wire"
        Just p -> Right p

    bubbleRight currentCtx currentTags acc pos target
      | pos >= target = Right (acc, currentCtx, currentTags)
      | otherwise = do
          swap <- swapAdjacent mode currentCtx pos
          acc' <- compD swap acc
          let ctx' = swapAt pos currentCtx
          let tags' = swapAt pos currentTags
          bubbleRight ctx' tags' acc' (pos + 1) target
