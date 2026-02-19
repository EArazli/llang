{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Kernel
  ( Doctrine
  , validateDoctrine
  , checkDoctrine
  , TypeExpr(..)
  , TypeArg(..)
  , TypeRef(..)
  , TypeName(..)
  , TyVar(..)
  , normalizeTypeDeep
  , normalizeTypeDeepWithCtx
  , normalizeTermDiagram
  , termExprToDiagramChecked
  , diagramToTermExprChecked
  , unifyTy
  , unifyTyFlex
  , SearchOutcome(..)
  , autoJoinProof
  ) where

import Data.Text (Text)
import Strat.Poly.Doctrine (Doctrine, validateDoctrine)
import Strat.Poly.Normalize (autoJoinProof)
import Strat.Poly.Proof (SearchOutcome(..))
import Strat.Poly.TypeExpr (TyVar(..), TypeArg(..), TypeExpr(..), TypeName(..), TypeRef(..))
import Strat.Poly.TypeNormalize
  ( normalizeTypeDeep
  , normalizeTypeDeepWithCtx
  , normalizeTermDiagram
  , termExprToDiagramChecked
  , diagramToTermExprChecked
  )
import Strat.Poly.UnifyTy (unifyTy, unifyTyFlex)


checkDoctrine :: Doctrine -> Either Text ()
checkDoctrine = validateDoctrine
