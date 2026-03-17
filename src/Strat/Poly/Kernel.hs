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
  , TmVar
  , tmvName
  , tmVarOwner
  , checkObjWellFormed
  , checkCodeWellFormed
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
  ( TmVar
  , tmvName
  , tmVarOwner
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
import Strat.Poly.DefEq
  ( checkObjWellFormed
  , checkCodeWellFormed
  , normalizeObjDeep
  , normalizeObjDeepWithCtx
  , normalizeCodeTermDeepWithCtx
  , normalizeTermDiagram
  , termExprToDiagramChecked
  , diagramToTermExprChecked
  )
import Strat.Poly.UnifyFlex (unifyObj, unifyObjFlex)


checkDoctrine :: Doctrine -> Either Text ()
checkDoctrine = validateDoctrine
