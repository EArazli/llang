{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.Poly.Kernel
  ( Doctrine
  , validateDoctrine
  , checkDoctrine
  , Obj(..)
  , ObjArg
  , CodeArg(..)
  , CodeTerm(..)
  , pattern OAObj
  , pattern OATm
  , pattern OVar
  , pattern OCon
  , pattern OMod
  , ObjRef(..)
  , ObjName(..)
  , ObjVar
  , pattern ObjVar
  , ovName
  , ovMode
  , normalizeObjDeep
  , normalizeObjDeepWithCtx
  , normalizeCodeTermDeepWithCtx
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
import Strat.Poly.Obj
  ( ObjVar
  , pattern ObjVar
  , ovName
  , ovMode
  , ObjArg
  , CodeArg(..)
  , CodeTerm(..)
  , pattern OAObj
  , pattern OATm
  , Obj(..)
  , pattern OVar
  , pattern OCon
  , pattern OMod
  , ObjName(..)
  , ObjRef(..)
  )
import Strat.Poly.ObjNormalize
  ( normalizeObjDeep
  , normalizeObjDeepWithCtx
  , normalizeCodeTermDeepWithCtx
  , normalizeTermDiagram
  , termExprToDiagramChecked
  , diagramToTermExprChecked
  )
import Strat.Poly.UnifyObj (unifyObj, unifyObjFlex)


checkDoctrine :: Doctrine -> Either Text ()
checkDoctrine = validateDoctrine
