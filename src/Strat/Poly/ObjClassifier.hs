{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ObjClassifier
  ( classifierOfMode
  , classifierModeForCtorUse
  , modeClassifierMode
  , modeUniverseObj
  , objCodeMode
  ) where

import qualified Data.Map.Strict as M
import Data.Text (Text)
import Strat.Poly.ModeTheory (ClassificationDecl(..), ModeName(..), ModeTheory(..))
import Strat.Poly.Obj (Obj(..), codeMode0, objOwnerMode)

classifierOfMode :: ModeTheory -> ModeName -> Maybe ClassificationDecl
classifierOfMode mt mode = M.lookup mode (mtClassifiedBy mt)

classifierModeForCtorUse :: ModeTheory -> ModeName -> Either Text ModeName
classifierModeForCtorUse mt ownerMode =
  case classifierOfMode mt ownerMode of
    Just decl -> Right (cdClassifier decl)
    Nothing ->
      Left
        ( "mode "
            <> renderMode ownerMode
            <> " is unclassified; add `mode "
            <> renderMode ownerMode
            <> " classifiedBy ... via ...;` before using object constructors"
        )
  where
    renderMode (ModeName m) = m

modeClassifierMode :: ModeTheory -> ModeName -> ModeName
modeClassifierMode mt mode =
  case classifierOfMode mt mode of
    Nothing -> mode
    Just decl -> cdClassifier decl

modeUniverseObj :: ModeTheory -> ModeName -> Maybe Obj
modeUniverseObj mt mode =
  cdUniverse <$> classifierOfMode mt mode

objCodeMode :: ModeTheory -> Obj -> ModeName
objCodeMode mt obj =
  case classifierOfMode mt (objOwnerMode obj) of
    Just decl -> cdClassifier decl
    Nothing -> codeMode0 (objCode obj)
