{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.CompObligations
  ( generateCompObligations
  , installGeneratedCompObligations
  , isGeneratedCompObligation
  ) where

import Data.Char (isAlphaNum)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Poly.DSL.AST (RawOblExpr(..), RawDiagExpr(..))
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , ObligationDecl(..)
  , GenDecl(..)
  , InputShape(..)
  )
import Strat.Poly.ModeTheory
  ( ModeName(..)
  , CompDecl(..)
  , ClassificationDecl(..)
  , ModeTheory(..)
  )
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Slots
  ( Slot(..)
  , SlotId(..)
  , SlotKind(..)
  , SlotSig(..)
  , extractDoctrineSlots
  )

isGeneratedCompObligation :: ObligationDecl -> Bool
isGeneratedCompObligation obl =
  obGenerated obl && "__comp/" `T.isPrefixOf` obName obl

data SlotLawProfile
  = SlotLawsFull
  | SlotLawsDomOnly
  | SlotLawsCodOnly
  | SlotLawsNone

data SlotBoundarySide
  = SlotOnDom
  | SlotOnCod
  | SlotSideUnknown

installGeneratedCompObligations :: Doctrine -> Either Text Doctrine
installGeneratedCompObligations doc = do
  generated <- generateCompObligations doc
  let keep = [ obl | obl <- dObligations doc, not (isGeneratedCompObligation obl) ]
  pure doc { dObligations = keep <> generated }

generateCompObligations :: Doctrine -> Either Text [ObligationDecl]
generateCompObligations doc = do
  slotsByGen <- extractDoctrineSlots doc
  pure (concatMap (genMode slotsByGen) (M.toList (mtClassifiedBy (dModes doc))))
  where
    genMode slotsByGen (mode, classDecl) =
      case cdComp classDecl of
        Nothing -> []
        Just compDecl ->
          concat
            [ lawsForSlot mode compDecl genName slot
            | ((m, genName), slots) <- M.toList slotsByGen
            , m == mode
            , slot <- slots
            ]

    lawsForSlot mode compDecl genName slot =
      case slotLawProfile mode genName slot of
        SlotLawsFull ->
          [ mkDomIdentityObligation mode compDecl genName slot
          , mkCodIdentityObligation mode compDecl genName slot
          , mkDomCompositionObligation mode compDecl genName slot
          , mkCodCompositionObligation mode compDecl genName slot
          , mkNaturalityObligation mode compDecl genName slot
          ]
        SlotLawsDomOnly ->
          [ mkDomIdentityObligation mode compDecl genName slot
          , mkDomCompositionObligation mode compDecl genName slot
          ]
        SlotLawsCodOnly ->
          [ mkCodIdentityObligation mode compDecl genName slot
          , mkCodCompositionObligation mode compDecl genName slot
          ]
        SlotLawsNone ->
          []

    mkDomIdentityObligation mode compDecl genName slot =
      let baseName =
            "__comp/"
              <> renderMode mode
              <> "/"
              <> renderGen genName
              <> "/"
              <> sanitizePath (sidPath (slotId slot))
              <> "/id_dom"
       in ObligationDecl
            { obName = baseName
            , obMode = mode
            , obForGen = True
            , obForGenName = Just genName
            , obGenerated = True
            , obParams = []
            , obDom = []
            , obCod = []
            , obLHSExpr =
                ROEComp
                  (ROELiftDom (compReindexDiag compDecl))
                  ROEGen
            , obRHSExpr = ROEGen
            , obPolicy = UseStructuralAsBidirectional
            }

    mkCodIdentityObligation mode compDecl genName slot =
      let baseName =
            "__comp/"
              <> renderMode mode
              <> "/"
              <> renderGen genName
              <> "/"
              <> sanitizePath (sidPath (slotId slot))
              <> "/id_cod"
       in ObligationDecl
            { obName = baseName
            , obMode = mode
            , obForGen = True
            , obForGenName = Just genName
            , obGenerated = True
            , obParams = []
            , obDom = []
            , obCod = []
            , obLHSExpr =
                ROEComp
                  ROEGen
                  (ROELiftCod (compReindexDiag compDecl))
            , obRHSExpr = ROEGen
            , obPolicy = UseStructuralAsBidirectional
            }

    mkDomCompositionObligation mode compDecl genName slot =
      let baseName =
            "__comp/"
              <> renderMode mode
              <> "/"
              <> renderGen genName
              <> "/"
              <> sanitizePath (sidPath (slotId slot))
              <> "/comp_dom"
       in ObligationDecl
            { obName = baseName
            , obMode = mode
            , obForGen = True
            , obForGenName = Just genName
            , obGenerated = True
            , obParams = []
            , obDom = []
            , obCod = []
            , obLHSExpr =
                ROEComp
                  (ROELiftDom (RDComp (compReindexDiag compDecl) (compReindexDiag compDecl)))
                  ROEGen
            , obRHSExpr =
                ROEComp
                  (ROELiftDom (compReindexDiag compDecl))
                  (ROEComp (ROELiftDom (compReindexDiag compDecl)) ROEGen)
            , obPolicy = UseStructuralAsBidirectional
            }

    mkCodCompositionObligation mode compDecl genName slot =
      let baseName =
            "__comp/"
              <> renderMode mode
              <> "/"
              <> renderGen genName
              <> "/"
              <> sanitizePath (sidPath (slotId slot))
              <> "/comp_cod"
       in ObligationDecl
            { obName = baseName
            , obMode = mode
            , obForGen = True
            , obForGenName = Just genName
            , obGenerated = True
            , obParams = []
            , obDom = []
            , obCod = []
            , obLHSExpr =
                ROEComp
                  ROEGen
                  (ROELiftCod (RDComp (compReindexDiag compDecl) (compReindexDiag compDecl)))
            , obRHSExpr =
                ROEComp
                  (ROEComp ROEGen (ROELiftCod (compReindexDiag compDecl)))
                  (ROELiftCod (compReindexDiag compDecl))
            , obPolicy = UseStructuralAsBidirectional
            }

    mkNaturalityObligation mode compDecl genName slot =
      let baseName =
            "__comp/"
              <> renderMode mode
              <> "/"
              <> renderGen genName
              <> "/"
              <> sanitizePath (sidPath (slotId slot))
              <> "/nat"
       in ObligationDecl
            { obName = baseName
            , obMode = mode
            , obForGen = True
            , obForGenName = Just genName
            , obGenerated = True
            , obParams = []
            , obDom = []
            , obCod = []
            , obLHSExpr =
                ROEComp
                  (ROELiftDom (compCtxExtDiag compDecl))
                  ROEGen
            , obRHSExpr =
                ROEComp
                  ROEGen
                  (ROELiftCod (compVarDiag compDecl))
            , obPolicy = UseStructuralAsBidirectional
            }

    compCtxExtDiag compDecl = compGenDiag (compCtxExt compDecl)
    compVarDiag compDecl = compGenDiag (compVar compDecl)
    compReindexDiag compDecl = compGenDiag (compReindex compDecl)

    compGenDiag genName =
      RDGen
        (renderGen genName)
        Nothing
        Nothing
        Nothing

    sanitizePath =
      T.map (\c -> if isAlphaNum c || c == '/' || c == '_' || c == '-' then c else '_')

    renderMode (ModeName n) = n
    renderGen (GenName n) = n

    slotLawProfile mode genName slot =
      case M.lookup mode (dGens doc) >>= M.lookup genName of
        Just gd -> slotProfileByGen mode gd slot
        Nothing -> SlotLawsNone

    slotProfileByGen mode gd slot =
      case slotKind slot of
        SlotBinder
          | hasOnlyBinderDom gd -> SlotLawsFull
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
