{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.Poly.Slots
  ( SlotKind(..)
  , SlotId(..)
  , SlotSig(..)
  , Slot(..)
  , extractGenSlots
  , extractGenSlotsWithTables
  , extractDoctrineSlots
  , extractDoctrineSlotsWithTables
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , GenDecl(..)
  , InputShape(..)
  , BinderSig(..)
  , CtorTables
  , deriveCtorTables
  , doctrineTypeTheoryFromTables
  , lookupCtorSigForOwnerInTables
  )
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
  ( CodeArg(..)
  , Obj(..)
  , TermDiagram(..)
  , tmVarOwner
  , pattern OVar
  , pattern OCon
  , pattern OMod
  , pattern OLift
  , pattern OAObj
  , pattern OATm
  )
import Strat.Poly.Tele (CtorSig(..), GenParam(..))
import Strat.Poly.Subst (bindHeadSubst)
import Strat.Poly.TermExpr (applyHeadSubstObj, structuralConvEnv)
import Strat.Poly.Syntax (Diagram(..), Edge(..), EdgePayload(..), BinderArg(..), TmVar(..))

data SlotKind
  = SlotBinder
  | SlotCtorTmArg
  deriving (Eq, Ord, Show)

data SlotId = SlotId
  { sidGen :: GenName
  , sidPath :: Text
  } deriving (Eq, Ord, Show)

data SlotSig
  = SlotBinderSig BinderSig
  | SlotTermSig
      { ssOwnerMode :: ModeName
      , ssSort :: Obj
      }
  deriving (Eq, Ord, Show)

data Slot = Slot
  { slotId :: SlotId
  , slotKind :: SlotKind
  , slotSig :: SlotSig
  } deriving (Eq, Ord, Show)

extractDoctrineSlots :: Doctrine -> Either Text (M.Map (ModeName, GenName) [Slot])
extractDoctrineSlots doc = do
  ctorTables <- deriveCtorTables doc
  extractDoctrineSlotsWithTables doc ctorTables

extractDoctrineSlotsWithTables
  :: Doctrine
  -> CtorTables
  -> Either Text (M.Map (ModeName, GenName) [Slot])
extractDoctrineSlotsWithTables doc ctorTables = do
  let allGens =
        [ (mode, gd)
        | (mode, table) <- M.toList (dGens doc)
        , gd <- M.elems table
        ]
  fmap M.fromList (mapM (one ctorTables) allGens)
  where
    one ctorTables (mode, gd) = do
      slots <- extractGenSlotsWithTables doc ctorTables gd
      Right ((mode, gdName gd), slots)

extractGenSlots :: Doctrine -> GenDecl -> Either Text [Slot]
extractGenSlots doc gd = do
  ctorTables <- deriveCtorTables doc
  extractGenSlotsWithTables doc ctorTables gd

extractGenSlotsWithTables :: Doctrine -> CtorTables -> GenDecl -> Either Text [Slot]
extractGenSlotsWithTables doc ctorTables gd = do
  tt <- doctrineTypeTheoryFromTables doc ctorTables
  let domOne (i, shape) =
        slotsInInputShape ("dom[" <> tshow i <> "]") shape
      codOne (i, ty) =
        slotsInObj ("cod[" <> tshow i <> "]") ty

      slotsInInputShape path shape =
        case shape of
          InPort ty ->
            slotsInObj path ty
          InBinder bs -> do
            let binderSlot =
                  Slot
                    { slotId = SlotId (gdName gd) path
                    , slotKind = SlotBinder
                    , slotSig = SlotBinderSig bs
                    }
            tmCtxSlots <- fmap concat (mapM (\(i, ty) -> slotsInObj (path <> ".tmctx[" <> tshow i <> "]") ty) (zip [0 :: Int ..] (bsTmCtx bs)))
            domSlots <- fmap concat (mapM (\(i, ty) -> slotsInObj (path <> ".binderDom[" <> tshow i <> "]") ty) (zip [0 :: Int ..] (bsDom bs)))
            codSlots <- fmap concat (mapM (\(i, ty) -> slotsInObj (path <> ".binderCod[" <> tshow i <> "]") ty) (zip [0 :: Int ..] (bsCod bs)))
            pure (binderSlot : tmCtxSlots <> domSlots <> codSlots)

      slotsInObj path ty =
        case ty of
          OVar _ ->
            Right []
          OLift _ inner ->
            slotsInObj (path <> ".lift") inner
          OCon ref args -> do
            sig <- lookupCtorSigForOwnerInTables doc ctorTables (objOwnerMode ty) ref
            if length (csParams sig) /= length args
              then
                Left
                  ( "slot extraction: constructor arity mismatch at "
                      <> renderGen (gdName gd)
                      <> "."
                      <> path
                  )
              else oneArgs path M.empty (zip [0 :: Int ..] (zip (csParams sig) args))

      oneArgs _ _ [] = Right []
      oneArgs path headSubst ((i, (param, arg)):rest) =
        let path' = path <> ".arg[" <> tshow i <> "]"
         in case (param, arg) of
              (GP_Ty v, OAObj innerTy) -> do
                inner <- slotsInObj path' innerTy
                headSubst' <- bindHeadSubst v (CAObj innerTy) headSubst
                (inner <>) <$> oneArgs path headSubst' rest
              (GP_Tm v, OATm tm) -> do
                sortTy <- applyHeadSubstObj tt (structuralConvEnv tt) (dTmCtx (unTerm tm)) headSubst (tmvSort v)
                nested <- slotsInTerm path' tm
                headSubst' <- bindHeadSubst v (CATm tm) headSubst
                restSlots <- oneArgs path headSubst' rest
                pure
                  ( Slot
                      { slotId = SlotId (gdName gd) path'
                      , slotKind = SlotCtorTmArg
                      , slotSig = SlotTermSig { ssOwnerMode = objOwnerMode sortTy, ssSort = sortTy }
                      }
                      : nested <> restSlots
                  )
              (GP_Tm _, OAObj _) ->
                Left ("slot extraction: expected term argument at " <> renderGen (gdName gd) <> "." <> path')
              (GP_Ty _, OATm _) ->
                Left ("slot extraction: expected type argument at " <> renderGen (gdName gd) <> "." <> path')

      slotsInTerm path (TermDiagram diag) =
        slotsInDiagram path diag

      slotsInDiagram path diag = do
        portSlots <- fmap concat (mapM portOne (zip [0 :: Int ..] (IM.toAscList (dPortObj diag))))
        tmCtxSlots <- fmap concat (mapM tmCtxOne (zip [0 :: Int ..] (dTmCtx diag)))
        edgeSlots <- fmap concat (mapM edgeOne (IM.toAscList (dEdges diag)))
        pure (portSlots <> tmCtxSlots <> edgeSlots)
        where
          portOne (i, (_, ty)) =
            slotsInObj (path <> ".term.port[" <> tshow i <> "]") ty

          tmCtxOne (i, ty) =
            slotsInObj (path <> ".term.tmctx[" <> tshow i <> "]") ty

          edgeOne (eid, edge) =
            case ePayload edge of
              PTmMeta tv ->
                slotsInObj (path <> ".term.edge[" <> tshow eid <> "].sort") (tmvSort tv)
              PGen _ _ bargs ->
                fmap concat (mapM (binderArgOne eid) (zip [0 :: Int ..] bargs))
              PBox _ inner ->
                slotsInDiagram (path <> ".term.edge[" <> tshow eid <> "].box") inner
              PFeedback inner ->
                slotsInDiagram (path <> ".term.edge[" <> tshow eid <> "].feedback") inner
              _ -> Right []

          binderArgOne eid (i, barg) =
            case barg of
              BAConcrete inner ->
                slotsInDiagram
                  (path <> ".term.edge[" <> tshow eid <> "].barg[" <> tshow i <> "]")
                  inner
              BAMeta _ -> Right []

      tshow :: Show a => a -> Text
      tshow = T.pack . show

      renderGen (GenName g) = g
  domSlots <- fmap concat (mapM domOne (zip [0 :: Int ..] (gdDom gd)))
  codSlots <- fmap concat (mapM codOne (zip [0 :: Int ..] (gdCod gd)))
  pure (domSlots <> codSlots)
