{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DiagramInfo
  ( freeVarsDiagram
  ) where

import qualified Data.IntMap.Strict as IM
import qualified Data.Set as S
import Strat.Poly.Graph
import Strat.Poly.Obj (TmVar, CodeArg(..), freeVarsObj, freeVarsTerm)
import Strat.Poly.Traversal (foldDiagram)

freeVarsDiagram :: Diagram -> S.Set TmVar
freeVarsDiagram =
  foldDiagram onDiag onPayload onCodeArg (\_ -> mempty)
  where
    onDiag d =
      S.unions
        [ S.unions (map freeVarsObj (IM.elems (dPortObj d)))
        , S.unions (map freeVarsObj (dTmCtx d))
        ]

    onPayload payload =
      case payload of
        PTmMeta v -> S.singleton v
        PTmLit _ -> S.empty
        _ -> S.empty

    onCodeArg arg =
      case arg of
        CAObj obj -> freeVarsObj obj
        CATm tm -> freeVarsTerm tm
