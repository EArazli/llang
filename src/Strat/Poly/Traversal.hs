{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Traversal
  ( foldDiagram
  , traverseDiagram
  ) where

import qualified Data.IntMap.Strict as IM
import Strat.Poly.Graph


foldDiagram
  :: Monoid m
  => (Diagram -> m)
  -> (EdgePayload -> m)
  -> (BinderArg -> m)
  -> Diagram
  -> m
foldDiagram onDiag onPayload onBArg = goDiag
  where
    goDiag d =
      onDiag d <> foldMap goEdge (IM.elems (dEdges d))

    goEdge e = goPayload (ePayload e)

    goPayload p =
      onPayload p
        <> case p of
          PGen _ _ bargs -> foldMap goBArg bargs
          PBox _ inner -> goDiag inner
          PFeedback inner -> goDiag inner
          PSplice _ -> mempty

    goBArg ba =
      onBArg ba
        <> case ba of
          BAConcrete inner -> goDiag inner
          BAMeta _ -> mempty


traverseDiagram
  :: Monad f
  => (Diagram -> f Diagram)
  -> (EdgePayload -> f EdgePayload)
  -> (BinderArg -> f BinderArg)
  -> Diagram
  -> f Diagram
traverseDiagram onDiag onPayload onBArg = goDiag
  where
    goDiag d = do
      edges' <- IM.traverseWithKey (\_ e -> goEdge e) (dEdges d)
      onDiag d { dEdges = edges' }

    goEdge e = do
      payload' <- goPayload (ePayload e)
      pure e { ePayload = payload' }

    goPayload p = do
      p' <-
        case p of
          PGen g attrs bargs -> do
            bargs' <- traverse goBArg bargs
            pure (PGen g attrs bargs')
          PBox name inner -> do
            inner' <- goDiag inner
            pure (PBox name inner')
          PFeedback inner -> do
            inner' <- goDiag inner
            pure (PFeedback inner')
          PSplice x ->
            pure (PSplice x)
      onPayload p'

    goBArg ba = do
      ba' <-
        case ba of
          BAConcrete inner -> BAConcrete <$> goDiag inner
          BAMeta x -> pure (BAMeta x)
      onBArg ba'
