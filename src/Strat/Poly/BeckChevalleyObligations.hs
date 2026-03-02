{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.BeckChevalleyObligations
  ( generateBeckChevalleyObligations
  , installGeneratedBeckChevalleyObligations
  , isGeneratedBeckChevalleyObligation
  ) where

import Data.Char (isAlphaNum)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Poly.DSL.AST (RawOblExpr(..), RawDiagExpr(..), RawModExpr(..))
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , ObligationDecl(..)
  , GenDecl(..)
  , InputShape(..)
  )
import Strat.Poly.ModeTheory
  ( ModeName(..)
  , ModName(..)
  , ModDecl(..)
  , CompDecl(..)
  , ClassificationDecl(..)
  , ModeTheory(..)
  , classifierLiftForModality
  )
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Slots
  ( Slot(..)
  , SlotId(..)
  , SlotKind(..)
  , SlotSig(..)
  , extractDoctrineSlots
  )

data SlotLawProfile
  = SlotLawsBothSides
  | SlotLawsDomOnly
  | SlotLawsCodOnly
  | SlotLawsNone

data SlotBoundarySide
  = SlotOnDom
  | SlotOnCod
  | SlotSideUnknown

isGeneratedBeckChevalleyObligation :: ObligationDecl -> Bool
isGeneratedBeckChevalleyObligation obl =
  obGenerated obl && "__bc/" `T.isPrefixOf` obName obl

installGeneratedBeckChevalleyObligations :: Doctrine -> Either Text Doctrine
installGeneratedBeckChevalleyObligations doc = do
  generated <- generateBeckChevalleyObligations doc
  let keep = [ obl | obl <- dObligations doc, not (isGeneratedBeckChevalleyObligation obl) ]
  pure doc { dObligations = keep <> generated }

generateBeckChevalleyObligations :: Doctrine -> Either Text [ObligationDecl]
generateBeckChevalleyObligations doc = do
  slotsByGen <- extractDoctrineSlots doc
  fmap concat (mapM (generateForModality slotsByGen) modalityInfos)
  where
    modalityInfos =
      [ (modName, decl, srcComp, tgtComp)
      | (modName, decl) <- M.toList (mtDecls (dModes doc))
      , Just srcClass <- [M.lookup (mdSrc decl) (mtClassifiedBy (dModes doc))]
      , Just tgtClass <- [M.lookup (mdTgt decl) (mtClassifiedBy (dModes doc))]
      , Just srcComp <- [cdComp srcClass]
      , Just tgtComp <- [cdComp tgtClass]
      , M.member modName (dActions doc)
      ]

    generateForModality slotsByGen (modName, decl, srcComp, tgtComp) = do
      _ <- classifierLiftForModality (dModes doc) modName
      let srcMode = mdSrc decl
      let srcSlots =
            [ (genName, slot)
            | ((mode, genName), slots) <- M.toList slotsByGen
            , mode == srcMode
            , slot <- slots
            ]
      pure
        ( concat
            [ lawsForSlot modName srcMode srcComp tgtComp genName slot
            | (genName, slot) <- srcSlots
            ]
        )

    lawsForSlot modName srcMode srcComp tgtComp genName slot =
      case slotLawProfile srcMode genName slot of
        SlotLawsBothSides ->
          [ mkDomObligation modName srcMode srcComp tgtComp genName slot
          , mkCodObligation modName srcMode srcComp tgtComp genName slot
          ]
        SlotLawsDomOnly ->
          [ mkDomObligation modName srcMode srcComp tgtComp genName slot ]
        SlotLawsCodOnly ->
          [ mkCodObligation modName srcMode srcComp tgtComp genName slot ]
        SlotLawsNone ->
          []

    mkDomObligation modName srcMode srcComp tgtComp genName slot =
      let rawMod = RMComp [renderMod modName]
       in ObligationDecl
            { obName = mkName modName srcMode genName slot "dom"
            , obMode = srcMode
            , obForGen = True
            , obForGenName = Just genName
            , obGenerated = True
            , obParams = []
            , obDom = []
            , obCod = []
            , obLHSExpr =
                ROEMap
                  rawMod
                  ( ROEComp
                      (ROELiftDom (compReindexDiag srcComp))
                      ROEGen
                  )
            , obRHSExpr =
                ROEComp
                  (ROELiftDom (compReindexDiag tgtComp))
                  (ROEMap rawMod ROEGen)
            , obPolicy = UseStructuralAsBidirectional
            }

    mkCodObligation modName srcMode srcComp tgtComp genName slot =
      let rawMod = RMComp [renderMod modName]
       in ObligationDecl
            { obName = mkName modName srcMode genName slot "cod"
            , obMode = srcMode
            , obForGen = True
            , obForGenName = Just genName
            , obGenerated = True
            , obParams = []
            , obDom = []
            , obCod = []
            , obLHSExpr =
                ROEMap
                  rawMod
                  ( ROEComp
                      ROEGen
                      (ROELiftCod (compReindexDiag srcComp))
                  )
            , obRHSExpr =
                ROEComp
                  (ROEMap rawMod ROEGen)
                  (ROELiftCod (compReindexDiag tgtComp))
            , obPolicy = UseStructuralAsBidirectional
            }

    mkName modName srcMode genName slot side =
      "__bc/"
        <> renderMod modName
        <> "/"
        <> renderMode srcMode
        <> "/"
        <> renderGen genName
        <> "/"
        <> sanitizePath (sidPath (slotId slot))
        <> "/"
        <> side

    compReindexDiag compDecl =
      RDGen
        (renderGen (compReindex compDecl))
        Nothing
        Nothing
        Nothing

    slotLawProfile mode genName slot =
      case M.lookup mode (dGens doc) >>= M.lookup genName of
        Just gd -> slotProfileByGen mode gd slot
        Nothing -> SlotLawsNone

    slotProfileByGen mode gd slot =
      case slotKind slot of
        SlotBinder
          | hasOnlyBinderDom gd -> SlotLawsBothSides
          | hasMixedDom gd -> SlotLawsNone
          | otherwise -> SlotLawsNone
        SlotCtorTmArg ->
          ctorSlotLawProfile mode slot

    ctorSlotLawProfile mode slot =
      case slotSig slot of
        SlotTermSig ownerMode _
          | ownerMode == mode ->
              case slotBoundarySide slot of
                SlotOnDom -> SlotLawsDomOnly
                SlotOnCod -> SlotLawsCodOnly
                SlotSideUnknown -> SlotLawsNone
          | otherwise -> SlotLawsNone
        SlotBinderSig _ -> SlotLawsNone

    slotBoundarySide slot =
      let path = sidPath (slotId slot)
       in if startsWith "dom[" path || ".binderDom[" `T.isInfixOf` path
            then SlotOnDom
            else
              if startsWith "cod[" path || ".binderCod[" `T.isInfixOf` path
                then SlotOnCod
                else SlotSideUnknown

    startsWith prefix txt = prefix `T.isPrefixOf` txt

    hasOnlyBinderDom gd =
      any isBinder (gdDom gd) && all isBinder (gdDom gd)

    hasMixedDom gd =
      any isBinder (gdDom gd) && any isPlainPort (gdDom gd)

    isPlainPort shape =
      case shape of
        InPort _ -> True
        InBinder _ -> False

    isBinder shape =
      case shape of
        InBinder _ -> True
        InPort _ -> False

    sanitizePath =
      T.map (\c -> if isAlphaNum c || c == '/' || c == '_' || c == '-' then c else '_')

    renderMode (ModeName n) = n
    renderMod (ModName n) = n
    renderGen (GenName n) = n
