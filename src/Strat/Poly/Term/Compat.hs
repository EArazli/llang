{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.Compat
  ( SharedTermDiagramContext(..)
  , unifyCtxCompat
  , unifyCtxFromPattern
  , termDiagramBoundarySorts
  , termDiagramOutputSort
  , sharedTermDiagramContext
  ) where

import Data.Text (Text)
import qualified Data.Set as S
import Strat.Poly.Graph (Diagram(..), diagramPortObj)
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Obj (Context, Obj, TermDiagram(..), TmVar, freeVarsObj, objOwnerMode)
import Strat.Poly.Subst (Subst)
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.UnifyFlex (unifyCtx)

data SharedTermDiagramContext = SharedTermDiagramContext
  { stdcMode :: ModeName
  , stdcTmCtx :: [Obj]
  , stdcBoundarySorts :: [Obj]
  , stdcExpectedSort :: Obj
  } deriving (Eq, Show)

unifyCtxCompat :: TypeTheory -> [Obj] -> Context -> Context -> Either Text Subst
unifyCtxCompat tt tmCtx ctxA ctxB =
  let flex = contextFlex (ctxA <> ctxB)
   in unifyCtx tt tmCtx flex ctxA ctxB

unifyCtxFromPattern :: TypeTheory -> [Obj] -> Context -> Context -> Either Text Subst
unifyCtxFromPattern tt tmCtx pat host =
  let flex = contextFlex pat
   in unifyCtx tt tmCtx flex pat host

termDiagramBoundarySorts :: Text -> Diagram -> Either Text [Obj]
termDiagramBoundarySorts label diag =
  mapM
    (\pid ->
        case diagramPortObj diag pid of
          Just ty -> Right ty
          Nothing -> Left (label <> ": missing boundary input sort")
    )
    (dIn diag)

termDiagramOutputSort :: Text -> Diagram -> Either Text Obj
termDiagramOutputSort label diag =
  case dOut diag of
    [pid] ->
      case diagramPortObj diag pid of
        Just ty -> Right ty
        Nothing -> Left (label <> ": missing output sort")
    _ -> Left (label <> ": term diagram must have exactly one output")

sharedTermDiagramContext :: Text -> TermDiagram -> TermDiagram -> Either Text SharedTermDiagramContext
sharedTermDiagramContext label lhsTm rhsTm = do
  let lhsDiag = unTerm lhsTm
      rhsDiag = unTerm rhsTm
      lhsMode = diagramEffectiveMode lhsDiag
      rhsMode = diagramEffectiveMode rhsDiag
  if lhsMode == rhsMode
    then pure ()
    else Left (label <> ": term diagrams have different modes")
  if dTmCtx lhsDiag == dTmCtx rhsDiag
    then pure ()
    else Left (label <> ": term diagrams have different ambient term contexts")
  if length (dIn lhsDiag) == length (dIn rhsDiag)
    then pure ()
    else Left (label <> ": term diagrams have different boundary arities")
  boundarySorts <- termDiagramBoundarySorts label lhsDiag
  expectedSort <- termDiagramOutputSort label lhsDiag
  pure
    SharedTermDiagramContext
      { stdcMode = lhsMode
      , stdcTmCtx = dTmCtx lhsDiag
      , stdcBoundarySorts = boundarySorts
      , stdcExpectedSort = expectedSort
      }
  where
    diagramEffectiveMode diag =
      case dOut diag of
        [pid] ->
          case diagramPortObj diag pid of
            Just ty -> objOwnerMode ty
            Nothing -> dMode diag
        _ -> dMode diag

contextFlex :: [Obj] -> S.Set TmVar
contextFlex = S.unions . map freeVarsObj
