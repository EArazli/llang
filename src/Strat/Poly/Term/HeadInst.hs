{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.HeadInst
  ( instantiateStoredHeadSubst
  , instantiateStructuralBinderSig
  , diagramBoundaryTypes
  , validateConcreteBinderDiagram
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as M
import Data.Text (Text)
import Strat.Poly.Graph
  ( Diagram(..)
  , PortId
  , diagramPortObj
  , validateDiagram
  )
import Strat.Poly.Obj
  ( Obj
  , TmVar(..)
  )
import Strat.Poly.Subst (bindHeadSubst)
import Strat.Poly.Syntax (CodeArg(..))
import Strat.Poly.TermExpr
  ( applyHeadSubstObj
  , structuralConvEnv
  )
import Strat.Poly.TypeTheory
  ( BinderSig(..)
  , TmHeadSig(..)
  , TypeTheory
  )
import Strat.Poly.Tele (GenParam(..))

instantiateStoredHeadSubst
  :: TypeTheory
  -> [Obj]
  -> TmHeadSig
  -> [CodeArg]
  -> Either Text (M.Map TmVar CodeArg)
instantiateStoredHeadSubst tt tmCtx sig args
  | length (thsParams sig) /= length args =
      Left "term head instantiation: stored-argument arity mismatch"
  | otherwise =
      foldM step M.empty (zip (thsParams sig) args)
  where
    step substAcc (param, arg) =
      case (param, arg) of
        (GP_Ty v, CAObj obj) -> do
          obj' <- applyHeadSubstObj tt (structuralConvEnv tt) tmCtx substAcc obj
          bindHeadSubst v (CAObj obj') substAcc
        (GP_Tm v, CATm tm) ->
          bindHeadSubst v (CATm tm) substAcc
        (GP_Ty _, CATm _) ->
          Left "term head instantiation: expected object-valued stored argument"
        (GP_Tm _, CAObj _) ->
          Left "term head instantiation: expected term-valued stored argument"

instantiateStructuralBinderSig
  :: TypeTheory
  -> [Obj]
  -> M.Map TmVar CodeArg
  -> BinderSig
  -> Either Text BinderSig
instantiateStructuralBinderSig tt tmCtx headSubst slot = do
  tmCtx0 <- mapM (applyHeadSubstObj tt (structuralConvEnv tt) tmCtx headSubst) (bsTmCtx slot)
  dom0 <- mapM (applyHeadSubstObj tt (structuralConvEnv tt) tmCtx0 headSubst) (bsDom slot)
  cod0 <- mapM (applyHeadSubstObj tt (structuralConvEnv tt) tmCtx0 headSubst) (bsCod slot)
  pure slot { bsTmCtx = tmCtx0, bsDom = dom0, bsCod = cod0 }

diagramBoundaryTypes :: Diagram -> [PortId] -> Either Text [Obj]
diagramBoundaryTypes diag =
  mapM
    ( \pid ->
        case diagramPortObj diag pid of
          Just ty -> Right ty
          Nothing -> Left "term head instantiation: missing binder boundary sort"
    )

validateConcreteBinderDiagram :: BinderSig -> Diagram -> Either Text ()
validateConcreteBinderDiagram slot inner = do
  validateDiagram inner
  if dTmCtx inner == bsTmCtx slot
    then Right ()
    else Left "term head instantiation: binder argument term-context mismatch"
  dom <- diagramBoundaryTypes inner (dIn inner)
  cod <- diagramBoundaryTypes inner (dOut inner)
  if dom == bsDom slot && cod == bsCod slot
    then Right ()
    else Left "term head instantiation: binder argument boundary mismatch"
