{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Normalize
  ( NormalizationStatus(..)
  , normalizeDiagramStatus
  , joinableWithinDiagram
  ) where

import Data.Text (Text)
import Strat.Kernel.Morphism (normalizeStatus, joinableWithin)
import Strat.Kernel.RewriteSystem (RewriteSystem)
import Strat.Kernel.Signature (Signature)
import Strat.Kernel.Syntax (Binder)
import Strat.Poly.Diagram (Diagram)
import Strat.Poly.Eval (diagramToTerm1)
import Strat.Poly.Compat (compileTermToDiagram)
import Strat.Poly.Doctrine (cartMode)


data NormalizationStatus a
  = Finished a
  | OutOfFuel a
  deriving (Eq, Show)

normalizeDiagramStatus
  :: Int
  -> RewriteSystem
  -> Signature
  -> [Binder]
  -> Diagram
  -> Either Text (NormalizationStatus Diagram)
normalizeDiagramStatus fuel rs sig tele diag = do
  term <- diagramToTerm1 sig tele diag
  let (nf, ok) = normalizeStatus fuel rs term
  diag' <- compileTermToDiagram sig cartMode tele nf
  pure (if ok then Finished diag' else OutOfFuel diag')

joinableWithinDiagram
  :: Int
  -> RewriteSystem
  -> Signature
  -> [Binder]
  -> Diagram
  -> Diagram
  -> Either Text Bool
joinableWithinDiagram fuel rs sig tele d1 d2 = do
  t1 <- diagramToTerm1 sig tele d1
  t2 <- diagramToTerm1 sig tele d2
  pure (joinableWithin fuel rs t1 t2)
