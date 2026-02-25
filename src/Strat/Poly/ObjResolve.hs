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
import Strat.Poly.ObjClassifier (classifierModeForCtorUse)

renderMode :: ModeName -> Text
renderMode (ModeName name) = name

resolveTypeRef :: Doctrine -> ModeName -> RawTypeRef -> Either Text ObjRef
resolveTypeRef doc ownerMode raw = do
  classifierMode <- requireClassifierForRawCtor doc ownerMode raw
  resolveTypeRefInClassifier doc ownerMode classifierMode raw

resolveTypeRefMaybe :: Doctrine -> ModeName -> RawTypeRef -> Either Text (Maybe ObjRef)
resolveTypeRefMaybe doc ownerMode raw = do
  classifierMode <- requireClassifierForRawCtor doc ownerMode raw
  resolveTypeRefInClassifierMaybe doc ownerMode classifierMode raw

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
resolveTypeRefInClassifierMaybeInTables doc tables ownerMode classifierMode raw = do
  expectedClassifier <- requireClassifierForRawCtor doc ownerMode raw
  if classifierMode == expectedClassifier
    then pure ()
    else
      Left
        ( "object of mode "
            <> renderMode ownerMode
            <> " is classified by "
            <> renderMode expectedClassifier
            <> "; resolver was asked to use "
            <> renderMode classifierMode
        )
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

requireClassifierForRawCtor :: Doctrine -> ModeName -> RawTypeRef -> Either Text ModeName
requireClassifierForRawCtor doc ownerMode raw =
  case classifierModeForCtorUse (dModes doc) ownerMode of
    Right mode -> Right mode
    Left err ->
      Left
        ( err
            <> " (while resolving constructor `"
            <> renderRawCtor raw
            <> "`)"
        )
  where
    renderRawCtor ref =
      case rtrMode ref of
        Just qualifier -> qualifier <> "." <> rtrName ref
        Nothing -> rtrName ref
