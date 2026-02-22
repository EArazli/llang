{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Kernel
  ( Doctrine
  , validateDoctrine
  , checkDoctrine
  , Obj(..)
  , ObjArg(..)
  , ObjRef(..)
  , ObjName(..)
  , ObjVar(..)
  , normalizeObjDeep
  , normalizeObjDeepWithCtx
  , normalizeTermDiagram
  , termExprToDiagramChecked
  , diagramToTermExprChecked
  , unifyObj
  , unifyObjFlex
  , SearchOutcome(..)
  , autoJoinProof
  ) where

import Data.Text (Text)
import Strat.Poly.Doctrine (Doctrine, validateDoctrine)
import Strat.Poly.Normalize (autoJoinProof)
import Strat.Poly.Proof (SearchOutcome(..))
import Strat.Poly.Obj (ObjVar(..), ObjArg(..), Obj(..), ObjName(..), ObjRef(..))
import Strat.Poly.ObjNormalize
  ( normalizeObjDeep
  , normalizeObjDeepWithCtx
  , normalizeTermDiagram
  , termExprToDiagramChecked
  , diagramToTermExprChecked
  )
import Strat.Poly.UnifyObj (unifyObj, unifyObjFlex)


checkDoctrine :: Doctrine -> Either Text ()
checkDoctrine = validateDoctrine
