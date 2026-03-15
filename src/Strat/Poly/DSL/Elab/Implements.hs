{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DSL.Elab.Implements
  ( ImplementsCheckResult(..)
  , ImplementsProof(..)
  , checkImplementsObligationsWithBudget
  , checkImplementsObligations
  ) where

import Control.Monad (foldM)
import Data.Char (isAlphaNum)
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Frontend.Env (ModuleEnv(..))
import Strat.Poly.DSL.AST
import Strat.Poly.DSL.Elab.Diag
  ( BinderMetaMode(..)
  , elabDiagExprWith
  , ensureAcyclicMode
  , mkForGenDiag
  , renderGenName
  , renderModeName
  , unifyBoundary
  )
import Strat.Poly.DSL.Elab.Resolve (elabRawModExpr)
import Strat.Poly.DSL.Elab.Term (ownerModeForTypeMeta)
import Strat.Poly.Diagram
import Strat.Poly.DiagramIso (diagramIsoEq)
import Strat.Poly.Doctrine
import Strat.Poly.Graph (BinderArg(..), Edge(..), EdgePayload(..), diagramPortObj)
import Strat.Poly.ModAction (applyModExpr)
import Strat.Poly.ModeTheory
import Strat.Poly.Morphism
import Strat.Poly.Normalize (NormalizationStatus(..), autoJoinProofWithMapper, normalizeWithMapper)
import Strat.Poly.Obj
import Strat.Poly.Proof
  ( JoinProof(..)
  , RewritePath(..)
  , SearchBudget(..)
  , SearchLimit
  , SearchOutcome(..)
  , defaultSearchBudget
  , renderSearchLimit
  , checkJoinProofWithMapper
  )
import Strat.Poly.Rewrite (rulesFromPolicy)
import Strat.Poly.Slots
  ( Slot(..)
  , SlotId(..)
  , SlotKind(..)
  , SlotSig(..)
  , extractDoctrineSlotsWithTables
  )
import Strat.Poly.TypeTheory (TypeTheory(..), ttCtorTablesByOwner)
import qualified Strat.Poly.UnifyObj as U

data ImplementsCheckResult
  = ImplementsCheckProved [(Text, ImplementsProof)]
  | ImplementsCheckUndecided Text SearchLimit
  deriving (Eq, Show)

data ImplementsProof
  = ImplementsProofJoin JoinProof
  | ImplementsProofDefEq
  deriving (Eq, Show)

data ForGenPrelude
  = ForGenPrelude Diagram Diagram

type ForGenPreludeCache = M.Map Text ForGenPrelude

checkImplementsObligationsWithBudget :: SearchBudget -> ModuleEnv -> Doctrine -> Morphism -> Doctrine -> Either Text ImplementsCheckResult
checkImplementsObligationsWithBudget budget env tgtDoc morph ifaceDoc = do
  ttTgt <- doctrineTypeTheory tgtDoc
  ttSrc <- doctrineTypeTheory (morSrc morph)
  let tgtCtorTables = ttCtorTablesByOwner ttTgt
  slotsByGen <- extractDoctrineSlotsWithTables tgtDoc tgtCtorTables
  snd <$> checkObligations M.empty ttSrc ttTgt tgtCtorTables slotsByGen (dObligations ifaceDoc)
  where
    checkObligations cache _ _ _ _ [] = Right (cache, ImplementsCheckProved [])
    checkObligations cache ttSrc ttTgt tgtCtorTables slotsByGen (obl:rest) = do
      (cache1, result) <- checkOne cache ttSrc ttTgt tgtCtorTables slotsByGen obl
      case result of
        ImplementsCheckUndecided{} -> Right (cache1, result)
        ImplementsCheckProved proofs -> do
          (cache2, restResult) <- checkObligations cache1 ttSrc ttTgt tgtCtorTables slotsByGen rest
          case restResult of
            ImplementsCheckUndecided{} -> Right (cache2, restResult)
            ImplementsCheckProved restProofs ->
              Right (cache2, ImplementsCheckProved (proofs <> restProofs))

    generatedCompRules = rulesFromPolicy UseOnlyComputationalLR (dCells2 tgtDoc)

    checkOne cache ttSrc ttTgt tgtCtorTables slotsByGen obl
      | obForGen obl = checkForGen cache ttSrc ttTgt tgtCtorTables slotsByGen obl
      | otherwise = checkPlain cache ttSrc ttTgt tgtCtorTables obl

    checkPlain cache ttSrc ttTgt tgtCtorTables obl = do
      tyVarsTgt <- mapM (mapObligationTyVar ttSrc ttTgt tgtCtorTables morph) (obTyVars obl)
      tmVarsTgt <- mapM (mapObligationTmVar ttSrc ttTgt tgtCtorTables morph) (obTmVars obl)
      lhs0 <- evalObligationExprMapped (obGenerated obl) ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (obMode obl) (obTyVars obl) (obTmVars obl) (obLHSExpr obl)
      rhs0 <- evalObligationExprMapped (obGenerated obl) ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (obMode obl) (obTyVars obl) (obTmVars obl) (obRHSExpr obl)
      domTgt <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables morph) (obDom obl)
      codTgt <- mapM (applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables morph) (obCod obl)
      let rigidTy = S.fromList tyVarsTgt
      let rigidTm = S.fromList tmVarsTgt
      lhs <- unifyBoundary ttTgt rigidTy rigidTm domTgt codTgt lhs0
      rhs <- unifyBoundary ttTgt rigidTy rigidTm domTgt codTgt rhs0
      let rules = rulesFromPolicy (obPolicy obl) (dCells2 tgtDoc)
      result <- checkObligationJoin ttTgt rules (obGenerated obl) (obName obl) lhs rhs
      pure (cache, result)

    checkForGen cache ttSrc ttTgt tgtCtorTables slotsByGen obl = do
      modeTgt <- applyMorphismMode morph (obMode obl)
      gens <- resolveForGenTargets tgtCtorTables modeTgt obl
      checkForGens cache ttSrc ttTgt tgtCtorTables slotsByGen modeTgt obl gens

    checkForGens cache _ _ _ _ _ _ [] = Right (cache, ImplementsCheckProved [])
    checkForGens cache ttSrc ttTgt tgtCtorTables slotsByGen modeTgt obl (gen:rest) = do
      (cache1, result) <- checkForGenOne cache ttSrc ttTgt tgtCtorTables slotsByGen modeTgt obl gen
      case result of
        ImplementsCheckUndecided{} -> Right (cache1, result)
        ImplementsCheckProved proofs -> do
          (cache2, restResult) <- checkForGens cache1 ttSrc ttTgt tgtCtorTables slotsByGen modeTgt obl rest
          case restResult of
            ImplementsCheckUndecided{} -> Right (cache2, restResult)
            ImplementsCheckProved restProofs ->
              Right (cache2, ImplementsCheckProved (proofs <> restProofs))

    checkForGenOne cache ttSrc ttTgt tgtCtorTables slotsByGen modeTgt obl gen = do
      genDiag <- mkForGenDiag modeTgt gen
      let rigidTy = S.fromList (gdTyVars gen)
      let rigidTm = S.fromList (gdTmVars gen)
      let label = obName obl <> "[" <> renderGenName (gdName gen) <> "]"
      directGeneratedOutcome <-
        case generatedSlotFor slotsByGen modeTgt gen obl of
          Just slot ->
            checkGeneratedSlotDirect ttSrc ttTgt tgtCtorTables gen genDiag obl label slot
          Nothing ->
            Right Nothing
      case directGeneratedOutcome of
        Just out ->
          Right (cache, out)
        Nothing ->
          fallbackForGen genDiag rigidTy rigidTm label
      where
        fallbackForGen genDiag rigidTy rigidTm label = do
          (cache1, ForGenPrelude lhsCommon rhsCommon) <-
            prepareForGenPrelude cache ttSrc ttTgt tgtCtorTables modeTgt obl gen genDiag
          (lhs, rhs) <-
            if obGenerated obl
              then Right (lhsCommon, rhsCommon)
              else do
                domGen <- diagramDom genDiag
                codGen <- diagramCod genDiag
                lhsLocked <-
                  case unifyBoundary ttTgt rigidTy rigidTm domGen codGen lhsCommon of
                    Left err ->
                      Left ("implements obligation " <> label <> ": boundary lock failed on lhs: " <> err)
                    Right lhs' ->
                      Right lhs'
                rhsLocked <-
                  case unifyBoundary ttTgt rigidTy rigidTm domGen codGen rhsCommon of
                    Left err ->
                      Left ("implements obligation " <> label <> ": boundary lock failed on rhs: " <> err)
                    Right rhs' ->
                      Right rhs'
                pure (lhsLocked, rhsLocked)
          let rules = rulesFromPolicy (obPolicy obl) (dCells2 tgtDoc)
          generatedSlotOutcome <- checkGeneratedSlot ttTgt slotsByGen modeTgt gen obl label lhs rhs
          case generatedSlotOutcome of
            Just out ->
              Right (cache1, out)
            Nothing -> do
              out <- checkObligationJoin ttTgt rules (obGenerated obl) label lhs rhs
              Right (cache1, out)

    checkGeneratedSlotDirect ttSrc ttTgt tgtCtorTables gen genDiag obl label slot =
      case slotKind slot of
        SlotCtorTmArg
          | isCodRootSlot slot ->
              checkGeneratedCodTermSlotDirect ttSrc ttTgt tgtCtorTables gen genDiag obl label slot
          | otherwise ->
              Right Nothing
        SlotBinder ->
          Right Nothing

    checkGeneratedCodTermSlotDirect ttSrc ttTgt tgtCtorTables gen genDiag obl label slot =
      case extractCtorSlotTerm gen slot genDiag of
        Left _ ->
          Right Nothing
        Right slotTm -> do
          let slotDiag = unTerm slotTm
          let rigidTy = S.fromList (gdTyVars gen)
          let rigidTm = S.fromList (gdTmVars gen)
          lhs0 <- evalObligationExprForGen (obGenerated obl) ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (obMode obl) (gdTyVars gen) (gdTmVars gen) slotDiag (obLHSExpr obl)
          rhs0 <- evalObligationExprForGen (obGenerated obl) ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (obMode obl) (gdTyVars gen) (gdTmVars gen) slotDiag (obRHSExpr obl)
          (lhsCommon, rhsCommon) <- inferCommonForGenBoundary ttTgt rigidTy rigidTm lhs0 rhs0
          lhsSeed <- normalizeForGeneratedObligation ttTgt [] lhsCommon
          rhsSeed <- normalizeForGeneratedObligation ttTgt [] rhsCommon
          same <- diagramIsoEq lhsSeed rhsSeed
          if same
            then Right (Just (ImplementsCheckProved [(label, ImplementsProofDefEq)]))
            else Right Nothing

    isCodRootSlot slot =
      "cod[" `T.isPrefixOf` sidPath (slotId slot)

    prepareForGenPrelude :: ForGenPreludeCache -> TypeTheory -> TypeTheory -> CtorTables -> ModeName -> ObligationDecl -> GenDecl -> Diagram -> Either Text (ForGenPreludeCache, ForGenPrelude)
    prepareForGenPrelude cache ttSrc ttTgt tgtCtorTables modeTgt obl gen genDiag =
      case M.lookup key cache of
        Just prep ->
          Right (cache, prep)
        Nothing -> do
          lhs0 <- evalObligationExprForGen (obGenerated obl) ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (obMode obl) (gdTyVars gen) (gdTmVars gen) genDiag (obLHSExpr obl)
          rhs0 <- evalObligationExprForGen (obGenerated obl) ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (obMode obl) (gdTyVars gen) (gdTmVars gen) genDiag (obRHSExpr obl)
          let rigidTy = S.fromList (gdTyVars gen)
          let rigidTm = S.fromList (gdTmVars gen)
          prep <- uncurry ForGenPrelude <$> inferCommonForGenBoundary ttTgt rigidTy rigidTm lhs0 rhs0
          pure (M.insert key prep cache, prep)
      where
        key =
          T.pack
            ( show
                ( modeTgt
                , gdName gen
                , obGenerated obl
                , obPolicy obl
                , obLHSExpr obl
                , obRHSExpr obl
                )
            )

    resolveForGenTargets tgtCtorTables modeTgt obl =
      case obForGenName obl of
        Nothing -> Right allModeGens
        Just srcGenName -> do
          tgtGenName <- mapForGenName (obMode obl) srcGenName
          case M.lookup modeTgt (dGens tgtDoc) >>= M.lookup tgtGenName of
            Nothing ->
              Left
                ( "implements obligation "
                    <> obName obl
                    <> ": missing target generator "
                    <> renderModeName modeTgt
                    <> "."
                    <> renderGenName tgtGenName
                )
            Just gd ->
              if isTypeDeclGenNameInTables tgtDoc tgtCtorTables modeTgt (ObjName (renderGenName tgtGenName))
                then
                  Left
                    ( "implements obligation "
                        <> obName obl
                        <> ": target generator "
                        <> renderModeName modeTgt
                        <> "."
                        <> renderGenName tgtGenName
                        <> " is constructor-like"
                    )
                else Right [gd]
      where
        compSupportNames =
          case M.lookup modeTgt (mtClassifiedBy (dModes tgtDoc)) >>= cdComp of
            Just comp ->
              S.fromList [compCtxExt comp, compVar comp, compReindex comp]
            Nothing -> S.empty
        allModeGens =
          [ gd
          | gd <- M.elems (M.findWithDefault M.empty modeTgt (dGens tgtDoc))
          , not (isTypeDeclGenNameInTables tgtDoc tgtCtorTables modeTgt (ObjName (renderGenName (gdName gd))))
          , gdName gd `S.notMember` compSupportNames
          ]

    mapForGenName modeSrc srcGenName =
      case M.lookup (modeSrc, srcGenName) (morGenMap morph) of
        Nothing -> Right srcGenName
        Just image ->
          case singleGeneratorImageName (giDiagram image) of
            Just tgtGenName -> Right tgtGenName
            Nothing ->
              Left
                ( "implements obligation: source generator "
                    <> renderModeName modeSrc
                    <> "."
                    <> renderGenName srcGenName
                    <> " maps to a non-singleton generator image"
                )

    singleGeneratorImageName diag =
      case IM.elems (dEdges diag) of
        [edge] ->
          case ePayload edge of
            PGen g _ _ 
              | eIns edge == dIn diag
              , eOuts edge == dOut diag ->
                  Just g
            _ -> Nothing
        _ -> Nothing

    checkGeneratedSlot tt slotsByGen modeTgt gen obl label lhs rhs =
      case generatedSlotFor slotsByGen modeTgt gen obl of
        Nothing -> Right Nothing
        Just slot -> do
          case slotKind slot of
            SlotCtorTmArg -> do
              let lhsTmE = extractCtorSlotTerm gen slot lhs
              let rhsTmE = extractCtorSlotTerm gen slot rhs
              case (lhsTmE, rhsTmE) of
                (Right lhsTm, Right rhsTm) ->
                  case slotSig slot of
                    SlotTermSig _ _sortTy -> do
                      let lhsCtx = dTmCtx (unTerm lhsTm)
                      let rhsCtx = dTmCtx (unTerm rhsTm)
                      case chooseHostTmCtx lhsCtx rhsCtx of
                        Nothing ->
                          Right Nothing
                        Just hostCtx -> do
                          lhsHost <- weakenDiagramTmCtxTo hostCtx (unTerm lhsTm)
                          rhsHost <- weakenDiagramTmCtxTo hostCtx (unTerm rhsTm)
                          lhsSeed <- normalizeForGeneratedObligation tt [] lhsHost
                          rhsSeed <- normalizeForGeneratedObligation tt [] rhsHost
                          same <- diagramIsoEq lhsSeed rhsSeed
                          if same
                            -- Generated slot obligations can be discharged directly on the designated
                            -- term slot once the generated computational seed normalizes both sides.
                            then Right (Just (ImplementsCheckProved [(label, ImplementsProofDefEq)]))
                            else Right Nothing
                    SlotBinderSig _ ->
                      Right Nothing
                _ ->
                  Right Nothing
            SlotBinder -> do
              let lhsArgE = extractBinderSlotArg gen slot lhs
              let rhsArgE = extractBinderSlotArg gen slot rhs
              case (lhsArgE, rhsArgE) of
                (Right lhsArg, Right rhsArg) -> do
                  ok <- defEqBinderArg tt lhsArg rhsArg
                  if ok
                    -- Slot-local binder obligations are discharged on the designated binder slot.
                    then Right (Just (ImplementsCheckProved [(label, ImplementsProofDefEq)]))
                    else Right Nothing
                _ ->
                  Right Nothing

    chooseHostTmCtx lhsCtx rhsCtx
      | lhsCtx == rhsCtx = Just lhsCtx
      | lhsCtx `L.isPrefixOf` rhsCtx = Just rhsCtx
      | rhsCtx `L.isPrefixOf` lhsCtx = Just lhsCtx
      | otherwise = Nothing

    inferCommonForGenBoundary tt rigidTy rigidTm lhs0 rhs0 = do
      hostTmCtx <-
        case chooseHostTmCtx (dTmCtx lhs0) (dTmCtx rhs0) of
          Nothing ->
            Left "implements obligation: for_gen sides have incompatible term contexts"
          Just tmCtx ->
            Right tmCtx
      lhsHost <- weakenDiagramTmCtxTo hostTmCtx lhs0
      rhsHost <- weakenDiagramTmCtxTo hostTmCtx rhs0
      domL <- diagramDom lhsHost
      domR <- diagramDom rhsHost
      let rigid = S.union rigidTy rigidTm
      let flex0 = S.difference (S.union (freeVarsDiagram lhsHost) (freeVarsDiagram rhsHost)) rigid
      sDom <- U.unifyCtx tt hostTmCtx flex0 domL domR
      lhs1 <- applySubstDiagram tt sDom lhsHost
      rhs1 <- applySubstDiagram tt sDom rhsHost
      codL <- diagramCod lhs1
      codR <- diagramCod rhs1
      let flex1 = S.difference (S.union (freeVarsDiagram lhs1) (freeVarsDiagram rhs1)) rigid
      sCod <- U.unifyCtx tt hostTmCtx flex1 codL codR
      lhs2 <- applySubstDiagram tt sCod lhs1
      rhs2 <- applySubstDiagram tt sCod rhs1
      pure (lhs2, rhs2)

    generatedSlotFor slotsByGen modeTgt gen obl = do
      slots <- M.lookup (modeTgt, gdName gen) slotsByGen
      key <- generatedSlotKey (obName obl)
      law <- generatedLawSuffix (obName obl)
      let matches =
            [ s
            | s <- slots
            , sanitizeGeneratedSlotPath (sidPath (slotId s)) == key
            , generatedSlotLawAllowed obl law gen s
            ]
      case matches of
        [slot] -> Just slot
        _ -> Nothing

    generatedSlotLawAllowed obl law _gen slot =
      if obGenerated obl && obForGen obl
        then
          case (slotKind slot, law) of
            (SlotCtorTmArg, "id_dom") -> True
            (SlotCtorTmArg, "id_cod") -> True
            (SlotCtorTmArg, "comp_dom") -> True
            (SlotCtorTmArg, "comp_cod") -> True
            (SlotBinder, "id_dom") -> True
            (SlotBinder, "id_cod") -> True
            (SlotBinder, "comp_dom") -> True
            (SlotBinder, "comp_cod") -> True
            (SlotBinder, "nat") -> True
            _ -> False
        else False

    generatedLawSuffix name =
      case reverse (T.splitOn "/" name) of
        law : _ -> Just law
        _ -> Nothing

    generatedSlotKey name =
      case T.splitOn "/" name of
        (_prefix : _mode : _gen : slotKey : _law : []) -> Just slotKey
        _ -> Nothing

    sanitizeGeneratedSlotPath =
      T.map (\c -> if isAlphaNum c || c == '/' || c == '_' || c == '-' then c else '_')

    extractBinderSlotArg :: GenDecl -> Slot -> Diagram -> Either Text BinderArg
    extractBinderSlotArg gen slot diag = do
      (domIdx, pathTail) <- parseBinderSlotPath (sidPath (slotId slot))
      if null pathTail
        then Right ()
        else Left "generated slot obligation: unsupported binder slot path"
      binderIdx <- binderArgIndexForDomSlot gen domIdx
      bargs <- uniqueGenBinderArgs (gdName gen) diag
      nth "binder argument" binderIdx bargs

    parseBinderSlotPath path =
      case T.splitOn "." path of
        [] ->
          Left "generated slot obligation: empty slot path"
        root : rest ->
          case parseIndexed "dom[" root of
            Just domIdx -> Right (domIdx, rest)
            Nothing -> Left "generated slot obligation: binder slot root must be dom[...]"

    binderArgIndexForDomSlot gen domIdx =
      if domIdx < 0 || domIdx >= length (gdDom gen)
        then Left "generated slot obligation: binder slot domain index out of bounds"
        else
          let before = take domIdx (gdDom gen)
           in case gdDom gen !! domIdx of
                InBinder _ ->
                  Right (length [() | InBinder _ <- before])
                InPort _ ->
                  Left "generated slot obligation: slot path points to non-binder domain input"

    uniqueGenBinderArgs g diag =
      case
        [ bargs
        | edge <- IM.elems (dEdges diag)
        , PGen g' _ bargs <- [ePayload edge]
        , g' == g
        ]
      of
        [bargs] -> Right bargs
        [] -> Left "generated slot obligation: generator edge not found while extracting binder slot"
        _ -> Left "generated slot obligation: multiple generator edges found while extracting binder slot"

    defEqBinderArg tt lhsArg rhsArg =
      case (lhsArg, rhsArg) of
        (BAMeta l, BAMeta r) ->
          Right (l == r)
        (BAConcrete lhsDiag0, BAConcrete rhsDiag0) ->
          case chooseHostTmCtx (dTmCtx lhsDiag0) (dTmCtx rhsDiag0) of
            Nothing ->
              Right False
            Just hostCtx -> do
              lhsDiag <- weakenDiagramTmCtxTo hostCtx lhsDiag0
              rhsDiag <- weakenDiagramTmCtxTo hostCtx rhsDiag0
              lhsSeed <- normalizeForGeneratedObligation tt [] lhsDiag
              rhsSeed <- normalizeForGeneratedObligation tt [] rhsDiag
              diagramIsoEq lhsSeed rhsSeed
        _ ->
          Right False

    extractCtorSlotTerm :: GenDecl -> Slot -> Diagram -> Either Text TermDiagram
    extractCtorSlotTerm gen slot diag = do
      let parts = T.splitOn "." (sidPath (slotId slot))
      case parts of
        [] ->
          Left "generated slot obligation: empty slot path"
        root : rest -> do
          (rootObj, tailSegs) <- extractRootObj gen root rest diag
          extractObjPath tailSegs rootObj

    extractRootObj gen seg rest diag
      | Just idx <- parseIndexed "dom[" seg =
          extractDomRootObj gen idx rest diag
      | Just idx <- parseIndexed "cod[" seg = do
          pid <- nth "codomain" idx (dOut diag)
          ty <- lookupPortTy "codomain" pid diag
          Right (ty, rest)
      | otherwise =
          Left "generated slot obligation: unsupported root slot path"

    extractDomRootObj gen domIdx rest diag =
      if domIdx < 0 || domIdx >= length (gdDom gen)
        then Left "generated slot obligation: domain index out of bounds"
        else
          case gdDom gen !! domIdx of
            InPort _ -> do
              let domPortIdx = length [() | InPort _ <- take domIdx (gdDom gen)]
              pid <- nth "domain" domPortIdx (dIn diag)
              ty <- lookupPortTy "domain" pid diag
              Right (ty, rest)
            InBinder _ -> do
              bdiag <- binderArgDiagramForDomSlot gen domIdx diag
              case rest of
                seg' : rest'
                  | Just idx <- parseIndexed "binderDom[" seg' -> do
                      pid <- nth "binder domain" idx (dIn bdiag)
                      ty <- lookupPortTy "binder domain" pid bdiag
                      Right (ty, rest')
                  | Just idx <- parseIndexed "binderCod[" seg' -> do
                      pid <- nth "binder codomain" idx (dOut bdiag)
                      ty <- lookupPortTy "binder codomain" pid bdiag
                      Right (ty, rest')
                  | Just idx <- parseIndexed "tmctx[" seg' -> do
                      ty <- nth "binder term context" idx (dTmCtx bdiag)
                      Right (ty, rest')
                _ ->
                  Left "generated slot obligation: binder ctor slot path must continue with binderDom/binderCod/tmctx"

    binderArgDiagramForDomSlot gen domIdx diag = do
      binderIdx <- binderArgIndexForDomSlot gen domIdx
      bargs <- uniqueGenBinderArgs (gdName gen) diag
      barg <- nth "binder argument" binderIdx bargs
      case barg of
        BAConcrete bdiag -> Right bdiag
        BAMeta _ -> Left "generated slot obligation: expected concrete binder argument for binder ctor slot path"

    extractObjPath segs obj =
      extractObjCodePath segs (objCode obj)

    extractObjCodePath segs code =
      case segs of
        [] ->
          Left "generated slot obligation: slot path does not end at a term argument"
        seg : rest
          | seg == "mod" ->
              case code of
                CTLift _ inner ->
                  extractObjCodePath rest inner
                _ ->
                  Left "generated slot obligation: expected modality wrapper in slot path"
          | Just idx <- parseIndexed "arg[" seg ->
              case code of
                CTCon _ args -> do
                  arg <- nth "constructor argument" idx args
                  case arg of
                    CATm tm ->
                      if null rest
                        then Right tm
                        else extractTermPath rest tm
                    CAObj ty ->
                      extractObjPath rest ty
                _ ->
                  Left "generated slot obligation: expected constructor in slot path"
          | otherwise ->
              Left "generated slot obligation: unsupported object slot segment"

    extractTermPath segs tm =
      case segs of
        "term" : rest -> stepTerm rest tm
        _ -> Left "generated slot obligation: expected term segment in slot path"
      where
        stepTerm [] term = Right term
        stepTerm (seg : rest) (TermDiagram termDiag)
          | Just idx <- parseIndexed "port[" seg = do
              ty <- nthIntMap "term port" idx (dPortObj termDiag)
              extractObjPath rest ty
          | Just idx <- parseIndexed "tmctx[" seg = do
              ty <- nth "term context" idx (dTmCtx termDiag)
              extractObjPath rest ty
          | Just idx <- parseIndexed "edge[" seg =
              case rest of
                "sort" : rest' -> do
                  edge <- nthIntMap "term edge" idx (dEdges termDiag)
                  case ePayload edge of
                    PTmMeta tv ->
                      extractObjPath rest' (tmvSort tv)
                    _ ->
                      Left "generated slot obligation: expected PTmMeta edge at term slot sort path"
                "box" : rest' -> do
                  edge <- nthIntMap "term edge" idx (dEdges termDiag)
                  case ePayload edge of
                    PBox _ inner ->
                      extractTermPath rest' (TermDiagram inner)
                    _ ->
                      Left "generated slot obligation: expected PBox edge at term slot box path"
                "feedback" : rest' -> do
                  edge <- nthIntMap "term edge" idx (dEdges termDiag)
                  case ePayload edge of
                    PFeedback inner ->
                      extractTermPath rest' (TermDiagram inner)
                    _ ->
                      Left "generated slot obligation: expected PFeedback edge at term slot feedback path"
                bargSeg : rest'
                  | Just bargIdx <- parseIndexed "barg[" bargSeg -> do
                      edge <- nthIntMap "term edge" idx (dEdges termDiag)
                      case ePayload edge of
                        PGen _ _ bargs -> do
                          barg <- nth "term binder argument" bargIdx bargs
                          case barg of
                            BAConcrete inner ->
                              extractTermPath rest' (TermDiagram inner)
                            BAMeta _ ->
                              Left "generated slot obligation: expected concrete term binder argument path"
                        _ ->
                          Left "generated slot obligation: expected PGen edge at term slot binder-arg path"
                _ ->
                  Left "generated slot obligation: expected .sort/.box/.feedback/.barg[...] after term edge segment"
          | otherwise =
              Left "generated slot obligation: unsupported term slot segment"

    parseIndexed prefix seg =
      if prefix `T.isPrefixOf` seg && "]" `T.isSuffixOf` seg
        then
          let inner = T.dropEnd 1 (T.drop (T.length prefix) seg)
           in case reads (T.unpack inner) of
                [(n, "")] -> Just n
                _ -> Nothing
        else Nothing

    nth label idx xs =
      if idx >= 0 && idx < length xs
        then Right (xs !! idx)
        else Left ("generated slot obligation: " <> label <> " index out of bounds")

    nthIntMap label idx table =
      case IM.lookup idx table of
        Just x -> Right x
        Nothing -> Left ("generated slot obligation: " <> label <> " index out of bounds")

    lookupPortTy label pid diag =
      case diagramPortObj diag pid of
        Just ty -> Right ty
        Nothing -> Left ("generated slot obligation: missing " <> label <> " port type")

    checkObligationJoin tt rules useGeneratedSeed label lhs rhs = do
      generatedOutcome <-
        if useGeneratedSeed
          then tryGeneratedSeed tt rules label lhs rhs
          else Right Nothing
      case generatedOutcome of
        Just out -> Right out
        Nothing -> runJoin tt rules label lhs rhs

    runJoin tt rules label lhs rhs = do
      proof <- autoJoinProofWithMapper (applyModExpr tgtDoc) tt budget rules lhs rhs
      case proof of
        SearchUndecided lim ->
          Right (ImplementsCheckUndecided label lim)
        SearchProved witness -> do
          checkJoinProofWithMapper (applyModExpr tgtDoc) tt rules witness
          Right (ImplementsCheckProved [(label, ImplementsProofJoin witness)])

    tryGeneratedSeed tt rules label lhs rhs = do
      lhsSeed <- normalizeForGeneratedObligation tt rules lhs
      rhsSeed <- normalizeForGeneratedObligation tt rules rhs
      same <- diagramIsoEq lhsSeed rhsSeed
      if same
        then do
          let witness =
                JoinProof
                  { jpLeft = RewritePath { rpStart = lhsSeed, rpSteps = [] }
                  , jpRight = RewritePath { rpStart = rhsSeed, rpSteps = [] }
                  }
          checkJoinProofWithMapper (applyModExpr tgtDoc) tt rules witness
          Right (Just (ImplementsCheckProved [(label, ImplementsProofJoin witness)]))
        else do
          seedProof <- autoJoinProofWithMapper (applyModExpr tgtDoc) tt budget rules lhsSeed rhsSeed
          case seedProof of
            SearchUndecided _ ->
              Right Nothing
            SearchProved witness -> do
              checkJoinProofWithMapper (applyModExpr tgtDoc) tt rules witness
              Right (Just (ImplementsCheckProved [(label, ImplementsProofJoin witness)]))

    normalizeForGeneratedObligation tt _rules diag =
      case generatedCompRules of
        [] -> Right diag
        _ -> do
          status <- normalizeWithMapper (applyModExpr tgtDoc) tt generatedSeedFuel generatedCompRules diag
          pure $
            case status of
              Finished d -> d
              OutOfFuel d -> d

    generatedSeedFuel =
      let depthFuel = max 1 (sbMaxDepth budget * 4)
       in min 256 depthFuel

checkImplementsObligations :: ModuleEnv -> Doctrine -> Morphism -> Doctrine -> Either Text ()
checkImplementsObligations env tgtDoc morph ifaceDoc = do
  result <- checkImplementsObligationsWithBudget defaultSearchBudget env tgtDoc morph ifaceDoc
  case result of
    ImplementsCheckProved _ ->
      Right ()
    ImplementsCheckUndecided label lim ->
      Left
        ( "implements obligation undecided: "
            <> label
            <> " ("
            <> renderSearchLimit lim
            <> ")"
        )

mapObligationTyVar :: TypeTheory -> TypeTheory -> CtorTables -> Morphism -> TmVar -> Either Text TmVar
mapObligationTyVar ttSrc ttTgt tgtCtorTables morph v = do
  ownerSrc <- ownerModeForTypeMeta (morSrc morph) v
  ownerTgt <- applyMorphismMode morph ownerSrc
  sort' <- applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables morph (tmvSort v)
  pure v { tmvSort = sort', tmvOwnerMode = Just ownerTgt }

mapObligationTmVar :: TypeTheory -> TypeTheory -> CtorTables -> Morphism -> TmVar -> Either Text TmVar
mapObligationTmVar ttSrc ttTgt tgtCtorTables morph v = do
  sort' <- applyMorphismTyWithCaches ttSrc ttTgt tgtCtorTables morph (tmvSort v)
  pure v { tmvSort = sort', tmvOwnerMode = Nothing }

evalObligationExprMapped
  :: Bool
  -> TypeTheory
  -> TypeTheory
  -> CtorTables
  -> ModuleEnv
  -> Doctrine
  -> Doctrine
  -> Morphism
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> RawOblExpr
  -> Either Text Diagram
evalObligationExprMapped allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars expr = do
  modeTgt <- applyMorphismMode morph mode
  case expr of
    ROEDiag rawDiag -> do
      diagSrc <- elabObligationDiag allowImplicitGenArgs env ifaceDoc mode [] tyVars tmVars rawDiag
      diagTgt <- applyMorphismDiagramWithTheories ttSrc ttTgt tgtCtorTables morph diagSrc
      if dMode diagTgt == modeTgt
        then Right diagTgt
        else Left "obligation: mapped diagram mode mismatch after morphism application"
    ROEMap rawMe innerExpr -> do
      me <- elabRawModExpr (dModes ifaceDoc) rawMe
      inner <- evalObligationExprMapped allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (meSrc me) tyVars tmVars innerExpr
      mappedMe <- applyMorphismModExpr morph me
      mapped <- applyModExpr tgtDoc mappedMe inner
      if dMode mapped == modeTgt
        then Right mapped
        else Left "obligation map: mapped diagram mode does not match surrounding expression mode"
    ROEGen ->
      Left "obligation: @gen is only valid in for_gen obligations"
    ROELiftDom _ ->
      Left "obligation: lift_dom is only valid in for_gen obligations"
    ROELiftCod _ ->
      Left "obligation: lift_cod is only valid in for_gen obligations"
    ROEComp a b -> do
      d1 <- evalObligationExprMapped allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars a
      d2 <- evalObligationExprMapped allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars b
      compD ttTgt d2 d1
    ROETensor a b -> do
      d1 <- evalObligationExprMapped allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars a
      d2 <- evalObligationExprMapped allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars b
      tensorD d1 d2

data LiftBoundary
  = LiftOverDom
  | LiftOverCod
  deriving (Eq, Show)

evalObligationExprForGen
  :: Bool
  -> TypeTheory
  -> TypeTheory
  -> CtorTables
  -> ModuleEnv
  -> Doctrine
  -> Doctrine
  -> Morphism
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> Diagram
  -> RawOblExpr
  -> Either Text Diagram
evalObligationExprForGen allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars genDiag expr = do
  modeTgt <- applyMorphismMode morph mode
  case expr of
    ROEDiag rawDiag -> do
      diagSrc <- elabObligationDiag allowImplicitGenArgs env ifaceDoc mode (dTmCtx genDiag) tyVars tmVars rawDiag
      diagTgt0 <- applyMorphismDiagramWithTheories ttSrc ttTgt tgtCtorTables morph diagSrc
      diagTgt <- weakenDiagramTmCtxTo (dTmCtx genDiag) diagTgt0
      if dMode diagTgt == modeTgt
        then Right diagTgt
        else Left "obligation: mapped diagram mode mismatch after morphism application"
    ROEMap rawMe innerExpr -> do
      me <- elabRawModExpr (dModes ifaceDoc) rawMe
      inner <- evalObligationExprForGen allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph (meSrc me) tyVars tmVars genDiag innerExpr
      mappedMe <- applyMorphismModExpr morph me
      mapped <- applyModExpr tgtDoc mappedMe inner
      if dMode mapped == modeTgt
        then Right mapped
        else Left "obligation map: mapped diagram mode does not match surrounding expression mode"
    ROEGen ->
      if dMode genDiag == modeTgt
        then Right genDiag
        else Left "obligation: @gen mode mismatch"
    ROELiftDom rawOp ->
      evalLiftedForAnchor allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode modeTgt tyVars tmVars genDiag LiftOverDom rawOp
    ROELiftCod rawOp ->
      evalLiftedForAnchor allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode modeTgt tyVars tmVars genDiag LiftOverCod rawOp
    ROEComp a b -> do
      case (a, b) of
        (ROELiftDom _rawDom, ROELiftCod _rawCod) ->
          Left "obligation: ambiguous composition anchor for lift_dom ; lift_cod"
        (ROELiftDom rawDom, _) -> do
          d2 <- evalObligationExprForGen allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars genDiag b
          d1 <- evalLiftedForAnchor allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode modeTgt tyVars tmVars d2 LiftOverDom rawDom
          compD ttTgt d2 d1
        (_, ROELiftCod rawCod) -> do
          d1 <- evalObligationExprForGen allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars genDiag a
          d2 <- evalLiftedForAnchor allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode modeTgt tyVars tmVars d1 LiftOverCod rawCod
          compD ttTgt d2 d1
        _ -> do
          d1 <- evalObligationExprForGen allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars genDiag a
          d2 <- evalObligationExprForGen allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars genDiag b
          compD ttTgt d2 d1
    ROETensor a b -> do
      d1 <- evalObligationExprForGen allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars genDiag a
      d2 <- evalObligationExprForGen allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc tgtDoc morph mode tyVars tmVars genDiag b
      tensorD d1 d2

evalLiftedForAnchor
  :: Bool
  -> TypeTheory
  -> TypeTheory
  -> CtorTables
  -> ModuleEnv
  -> Doctrine
  -> Doctrine
  -> Morphism
  -> ModeName
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> Diagram
  -> LiftBoundary
  -> RawDiagExpr
  -> Either Text Diagram
evalLiftedForAnchor _allowImplicitGenArgs ttSrc ttTgt tgtCtorTables env ifaceDoc _tgtDoc morph modeSrc modeTgt tyVars tmVars anchorDiag liftSide rawOp = do
  let ttDoc = ttTgt
  opSrc <- elabObligationDiag True env ifaceDoc modeSrc (dTmCtx anchorDiag) tyVars tmVars rawOp
  opTgt0 <- applyMorphismDiagramWithTheories ttSrc ttTgt tgtCtorTables morph opSrc
  opTgt <- weakenDiagramTmCtxTo (dTmCtx anchorDiag) opTgt0
  if dMode opTgt == modeTgt
    then Right ()
    else Left "obligation: mapped diagram mode mismatch after morphism application"
  dom0 <- diagramDom opTgt
  if length dom0 /= 1
    then Left (sideLabel <> ": operator must have exactly one input ([x] -> [...])")
    else Right ()
  ctx <- case liftSide of
    LiftOverDom -> diagramDom anchorDiag
    LiftOverCod -> diagramCod anchorDiag
  ops <- mapM (instantiateAt ttDoc opTgt dom0) ctx
  case ops of
    [] -> Right (idDTm modeTgt (dTmCtx anchorDiag) [])
    (d0:rest) -> foldM tensorD d0 rest
  where
    rigidTy = S.fromList tyVars
    rigidTm = S.fromList tmVars
    sideLabel =
      case liftSide of
        LiftOverDom -> "lift_dom"
        LiftOverCod -> "lift_cod"

    instantiateAt ttDoc opTgt dom0 argTy = do
      let flex = S.difference (freeVarsDiagram opTgt) (S.union rigidTy rigidTm)
      sDom <- U.unifyCtx ttDoc (dTmCtx opTgt) flex dom0 [argTy]
      applySubstDiagram ttDoc sDom opTgt

elabObligationDiag
  :: Bool
  -> ModuleEnv
  -> Doctrine
  -> ModeName
  -> [Obj]
  -> [TmVar]
  -> [TmVar]
  -> RawDiagExpr
  -> Either Text Diagram
elabObligationDiag allowImplicitGenArgs env doc mode tmCtx tyVars tmVars rawDiag = do
  (diag, _) <- elabDiagExprWith env doc mode tmCtx tyVars tmVars M.empty BMNoMeta False allowImplicitGenArgs rawDiag
  ensureAcyclicMode doc mode diag
  pure diag
