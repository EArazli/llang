{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Diagram
  ( GenLabel(..)
  , Diagram(..)
  , idD
  , genD
  , compD
  , tensorD
  , diagramDom
  , diagramCod
  ) where

import Data.Text (Text)
import Strat.Kernel.Syntax (OpName)
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.TypeExpr (Context, TypeExpr)


data GenLabel
  = GLUser OpName
  | GLDup TypeExpr
  | GLDrop TypeExpr
  | GLSwap TypeExpr TypeExpr
  deriving (Eq, Ord, Show)


data Diagram
  = DId ModeName Context
  | DGen ModeName Context Context GenLabel
  | DComp Diagram Diagram
  | DTensor Diagram Diagram
  deriving (Eq, Show)

idD :: ModeName -> Context -> Diagram
idD = DId

genD :: ModeName -> Context -> Context -> GenLabel -> Diagram
genD = DGen

compD :: Diagram -> Diagram -> Either Text Diagram
compD g f
  | diagramMode g /= diagramMode f = Left "diagram composition mode mismatch"
  | diagramCod f /= diagramDom g = Left "diagram composition boundary mismatch"
  | otherwise = Right (DComp g f)


tensorD :: Diagram -> Diagram -> Either Text Diagram
tensorD f g
  | diagramMode f /= diagramMode g = Left "diagram tensor mode mismatch"
  | otherwise = Right (DTensor f g)


diagramDom :: Diagram -> Context
diagramDom (DId _ ctx) = ctx
diagramDom (DGen _ dom _ _) = dom
diagramDom (DComp _ f) = diagramDom f
diagramDom (DTensor f g) = diagramDom f <> diagramDom g


diagramCod :: Diagram -> Context
diagramCod (DId _ ctx) = ctx
diagramCod (DGen _ _ cod _) = cod
diagramCod (DComp g _) = diagramCod g
diagramCod (DTensor f g) = diagramCod f <> diagramCod g


diagramMode :: Diagram -> ModeName
diagramMode (DId mode _) = mode
diagramMode (DGen mode _ _ _) = mode
diagramMode (DComp g _) = diagramMode g
diagramMode (DTensor f _) = diagramMode f
