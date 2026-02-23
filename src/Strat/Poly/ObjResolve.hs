{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ObjResolve
  ( resolveTypeRef
  , resolveTypeRefInClassifier
  ) where

import qualified Data.Map.Strict as M
import Data.Text (Text)
import Strat.Poly.DSL.AST (RawTypeRef(..))
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.Obj (ObjName(..), ObjRef(..))
import Strat.Poly.ObjClassifier (modeClassifierMode)

resolveTypeRef :: Doctrine -> ModeName -> RawTypeRef -> Either Text ObjRef
resolveTypeRef doc ownerMode =
  resolveTypeRefInClassifier doc ownerMode (modeClassifierMode (dModes doc) ownerMode)

resolveTypeRefInClassifier
  :: Doctrine
  -> ModeName
  -> ModeName
  -> RawTypeRef
  -> Either Text ObjRef
resolveTypeRefInClassifier doc ownerMode classifierMode raw =
  case rtrMode raw of
    Just modeName -> do
      let qualifier = ModeName modeName
      ensureMode qualifier
      if qualifier == classifierMode
        then lookupQualified qualifier
        else
          Left
            ( "object of mode "
                <> renderMode ownerMode
                <> " is classified by "
                <> renderMode classifierMode
                <> "; constructor qualifier "
                <> modeName
                <> " is not allowed here"
            )
    Nothing ->
      lookupQualified classifierMode
  where
    tname = ObjName (rtrName raw)

    ensureMode mode =
      if M.member mode (mtModes (dModes doc))
        then Right ()
        else Left ("unknown mode: " <> renderMode mode)

    lookupQualified mode =
      case M.lookup mode (dTypes doc) >>= M.lookup tname of
        Nothing -> Left ("unknown type constructor: " <> rtrName raw)
        Just _ -> Right (ObjRef mode tname)

    renderMode (ModeName name) = name
