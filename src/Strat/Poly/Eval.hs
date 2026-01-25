{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Eval
  ( evalDiagram
  , diagramToTerm1
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Strat.Kernel.Syntax (Binder(..), Term)
import Strat.Kernel.Term (mkOp, mkVar)
import Strat.Kernel.Signature (Signature)
import Strat.Poly.Diagram


evalDiagram :: Signature -> [Binder] -> Diagram -> Either Text [Term]
evalDiagram sig tele diagram =
  evalWithEnv sig (map (\b -> mkVar (bSort b) (bVar b)) tele) diagram


diagramToTerm1 :: Signature -> [Binder] -> Diagram -> Either Text Term
diagramToTerm1 sig tele diagram = do
  terms <- evalDiagram sig tele diagram
  case terms of
    [t] -> Right t
    _ -> Left "diagramToTerm1: expected single output"


evalWithEnv :: Signature -> [Term] -> Diagram -> Either Text [Term]
evalWithEnv sig env diagram =
  case diagram of
    DId _ _ -> Right env
    DGen _ _ _ label -> evalGen sig label env
    DComp g f -> do
      mid <- evalWithEnv sig env f
      evalWithEnv sig mid g
    DTensor f g -> do
      let domF = length (diagramDom f)
      let domG = length (diagramDom g)
      if length env /= domF + domG
        then Left "tensor evaluation: input size mismatch"
        else do
          let (envF, envG) = splitAt domF env
          outF <- evalWithEnv sig envF f
          outG <- evalWithEnv sig envG g
          Right (outF <> outG)


evalGen :: Signature -> GenLabel -> [Term] -> Either Text [Term]
evalGen sig label inputs =
  case label of
    GLUser op -> do
      case mkOp sig op inputs of
        Left err -> Left (T.pack (show err))
        Right term -> Right [term]
    GLDup _ ->
      case inputs of
        [t] -> Right [t, t]
        _ -> Left "GLDup expects one input"
    GLDrop _ ->
      case inputs of
        [_] -> Right []
        _ -> Left "GLDrop expects one input"
    GLSwap _ _ ->
      case inputs of
        [x, y] -> Right [y, x]
        _ -> Left "GLSwap expects two inputs"
