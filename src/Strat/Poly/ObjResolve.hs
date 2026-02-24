{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ObjResolve
  ( resolveTypeRef
  , resolveTypeRefMaybe
  , resolveTypeRefInClassifier
  , resolveTypeRefInClassifierMaybe
  , resolveTypeRefInClassifierInTables
  , resolveTypeRefInClassifierMaybeInTables
  ) where

import qualified Data.Map.Strict as M
import Data.Text (Text)
import Strat.Poly.DSL.AST (RawTypeRef(..))
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , CtorTables
  , deriveCtorTables
  , lookupCtorRefForOwnerInTables
  )
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..))
import Strat.Poly.Obj (ObjName(..), ObjRef(..))
import Strat.Poly.ObjClassifier (modeClassifierMode)

renderMode :: ModeName -> Text
renderMode (ModeName name) = name

resolveTypeRef :: Doctrine -> ModeName -> RawTypeRef -> Either Text ObjRef
resolveTypeRef doc ownerMode =
  resolveTypeRefInClassifier doc ownerMode (modeClassifierMode (dModes doc) ownerMode)

resolveTypeRefMaybe :: Doctrine -> ModeName -> RawTypeRef -> Either Text (Maybe ObjRef)
resolveTypeRefMaybe doc ownerMode =
  resolveTypeRefInClassifierMaybe doc ownerMode (modeClassifierMode (dModes doc) ownerMode)

resolveTypeRefInClassifier
  :: Doctrine
  -> ModeName
  -> ModeName
  -> RawTypeRef
  -> Either Text ObjRef
resolveTypeRefInClassifier doc ownerMode classifierMode raw = do
  tables <- deriveCtorTables doc
  mRef <- resolveTypeRefInClassifierMaybeInTables doc tables ownerMode classifierMode raw
  case mRef of
    Just ref -> Right ref
    Nothing ->
      Left
        ( "unknown type constructor: "
            <> rtrName raw
            <> " (object mode "
            <> renderMode ownerMode
            <> " is classified by "
            <> renderMode classifierMode
            <> "; looked in classifier mode "
            <> renderMode classifierMode
            <> ")"
        )

resolveTypeRefInClassifierMaybe
  :: Doctrine
  -> ModeName
  -> ModeName
  -> RawTypeRef
  -> Either Text (Maybe ObjRef)
resolveTypeRefInClassifierMaybe doc ownerMode classifierMode raw = do
  tables <- deriveCtorTables doc
  resolveTypeRefInClassifierMaybeInTables doc tables ownerMode classifierMode raw

resolveTypeRefInClassifierInTables
  :: Doctrine
  -> CtorTables
  -> ModeName
  -> ModeName
  -> RawTypeRef
  -> Either Text ObjRef
resolveTypeRefInClassifierInTables doc tables ownerMode classifierMode raw = do
  mRef <- resolveTypeRefInClassifierMaybeInTables doc tables ownerMode classifierMode raw
  case mRef of
    Just ref -> Right ref
    Nothing ->
      Left
        ( "unknown type constructor: "
            <> rtrName raw
            <> " (object mode "
            <> renderMode ownerMode
            <> " is classified by "
            <> renderMode classifierMode
            <> "; looked in classifier mode "
            <> renderMode classifierMode
            <> ")"
        )

resolveTypeRefInClassifierMaybeInTables
  :: Doctrine
  -> CtorTables
  -> ModeName
  -> ModeName
  -> RawTypeRef
  -> Either Text (Maybe ObjRef)
resolveTypeRefInClassifierMaybeInTables doc tables ownerMode classifierMode raw =
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

    lookupQualified mode = do
      let mRef = lookupCtorRefForOwnerInTables doc tables ownerMode tname
      pure
        ( case mRef of
            Just ref
              | orMode ref == mode -> Just ref
            _ -> Nothing
        )
