{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Traversal
  ( foldDiagram
  , traverseDiagram
  ) where

import qualified Data.IntMap.Strict as IM
import Strat.Poly.Graph
import Strat.Poly.Syntax (CodeArg(..), TermDiagram(..))


foldDiagram
  :: Monoid m
  => (Diagram -> m)
  -> (EdgePayload -> m)
  -> (CodeArg -> m)
  -> (BinderArg -> m)
  -> Diagram
  -> m
foldDiagram onDiag onPayload onCodeArg onBArg = goDiag
  where
    goDiag d =
      onDiag d <> foldMap goEdge (IM.elems (dEdges d))

    goEdge e = goPayload (ePayload e)

    goPayload p =
      onPayload p
        <> case p of
          PGen _ args bargs -> foldMap goCodeArg args <> foldMap goBArg bargs
          PProvider _ -> mempty
          PModuleRef _ -> mempty
          PBox _ inner -> goDiag inner
          PFeedback inner -> goDiag inner
          PSplice _ _ -> mempty
          PTmMeta _ -> mempty
          PTmLit _ -> mempty
          PInternalDrop -> mempty

    goCodeArg arg =
      onCodeArg arg
        <> case arg of
          CAObj _ -> mempty
          CATm (TermDiagram inner) -> goDiag inner

    goBArg ba =
      onBArg ba
        <> case ba of
          BAConcrete inner -> goDiag inner
          BAMeta _ -> mempty


traverseDiagram
  :: Monad f
  => (Diagram -> f Diagram)
  -> (EdgePayload -> f EdgePayload)
  -> (CodeArg -> f CodeArg)
  -> (BinderArg -> f BinderArg)
  -> Diagram
  -> f Diagram
traverseDiagram onDiag onPayload onCodeArg onBArg = goDiag
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
          PGen g args bargs -> do
            args' <- traverse goCodeArg args
            bargs' <- traverse goBArg bargs
            pure (PGen g args' bargs')
          PProvider ref ->
            pure (PProvider ref)
          PModuleRef ref ->
            pure (PModuleRef ref)
          PBox name inner -> do
            inner' <- goDiag inner
            pure (PBox name inner')
          PFeedback inner -> do
            inner' <- goDiag inner
            pure (PFeedback inner')
          PSplice x me ->
            pure (PSplice x me)
          PTmMeta v ->
            pure (PTmMeta v)
          PTmLit lit ->
            pure (PTmLit lit)
          PInternalDrop ->
            pure PInternalDrop
      onPayload p'

    goCodeArg arg = do
      arg' <-
        case arg of
          CAObj obj -> pure (CAObj obj)
          CATm (TermDiagram inner) -> CATm . TermDiagram <$> goDiag inner
      onCodeArg arg'

    goBArg ba = do
      ba' <-
        case ba of
          BAConcrete inner -> BAConcrete <$> goDiag inner
          BAMeta x -> pure (BAMeta x)
      onBArg ba'
