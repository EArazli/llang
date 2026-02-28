{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DSL.Elab.Build
  ( BuildOps(..)
  , ElabState(..)
  , seedDoctrine
  , applyPendingDeclarations
  , refreshPendingClassificationsBestEffort
  ) where

import Control.Monad (foldM)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.DSL.AST (RawCompDecl(..), RawPolyObjExpr(..), RawTypeRef(..))
import Strat.Poly.DSL.Elab.PhaseTypes
  ( ClassificationDeclRaw(..)
  , UniverseSpec(..)
  )
import Strat.Poly.Diagram (Diagram(..))
import Strat.Poly.Doctrine
  ( BinderSig(..)
  , CtorTables
  , Doctrine(..)
  , GenDecl(..)
  , GenParam(..)
  , InputShape(..)
  , ModAction(..)
  , ObligationDecl(..)
  , deriveCtorTables
  , isTypeDeclGenNameInTables
  )
import Strat.Poly.ModeTheory
  ( ClassificationDecl(..)
  , CompDecl(..)
  , ModeName(..)
  , ModeTheory(..)
  , addClassification
  , emptyModeTheory
  )
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj
  ( CodeArg(..)
  , CodeTerm(..)
  , Obj(..)
  , ObjName(..)
  , TmMeta(..)
  , TmVar(..)
  , TermDiagram(..)
  , objVarToTmVar
  , tmVarToObjVar
  )
import Strat.Poly.ObjClassifier (modeUniverseObj)
import Strat.Poly.Graph (BinderArg(..), Edge(..), EdgePayload(..))

data BuildOps = BuildOps
  { boResolveSeedUniverse :: Doctrine -> ModeName -> RawPolyObjExpr -> Either Text Obj
  , boElabUniverseWithTables :: Doctrine -> CtorTables -> ModeName -> RawPolyObjExpr -> Either Text Obj
  }

data ElabState = ElabState
  { esDoc :: Doctrine
  , esPendingClass :: [(ModeName, ClassificationDeclRaw)]
  , esPendingComp :: [RawCompDecl]
  }

seedDoctrine :: Text -> Maybe Doctrine -> Doctrine
seedDoctrine name base =
  case base of
    Nothing ->
      Doctrine
        { dName = name
        , dModes = emptyModeTheory
        , dAcyclicModes = S.empty
        , dAttrSorts = M.empty
        , dGens = M.empty
        , dCells2 = []
        , dActions = M.empty
        , dObligations = []
        }
    Just doc -> doc { dName = name, dAttrSorts = dAttrSorts doc }

applyPendingDeclarations :: BuildOps -> ElabState -> Either Text Doctrine
applyPendingDeclarations ops st = do
  doc <- applyPendingClassificationsFinal ops st
  doc' <- applyPendingComprehensions st doc
  pure (materializeResolvedUniverses ops st doc')

refreshPendingClassificationsBestEffort :: BuildOps -> ElabState -> ElabState
refreshPendingClassificationsBestEffort ops st =
  case applyPendingClassificationsBestEffort ops st of
    Left _ -> st
    Right doc -> st { esDoc = materializeResolvedUniverses ops st doc }

materializeResolvedUniverses :: BuildOps -> ElabState -> Doctrine -> Doctrine
materializeResolvedUniverses ops st doc =
  doc
    { dGens = M.map (M.map rewriteGen) (dGens doc)
    , dCells2 = map rewriteCell (dCells2 doc)
    , dActions = M.map rewriteAction (dActions doc)
    , dObligations = map rewriteObligation (dObligations doc)
    }
  where
    newClasses = mtClassifiedBy (dModes doc)

    replacementByOwner =
      M.fromList
        [ (ownerMode, (seedUniverse, newUniverse))
        | (ownerMode, rawClass) <- esPendingClass st
        , Just newDecl <- [M.lookup ownerMode newClasses]
        , Right seedUniverse <- [seedUniverseForRaw doc rawClass]
        , let newUniverse = cdUniverse newDecl
        , seedUniverse /= newUniverse
        ]

    seedUniverseForRaw doc0 rawClass =
      case cdrUniverse rawClass of
        UniverseResolved u -> Right u
        UniverseRaw rawUniverse ->
          boResolveSeedUniverse ops doc0 (cdrClassifier rawClass) rawUniverse

    rewriteObj obj =
      case M.lookup (objOwnerMode obj) replacementByOwner of
        Just (seedUniverse, resolvedUniverse)
          | obj == seedUniverse ->
              resolvedUniverse
        _ ->
          obj { objCode = rewriteCode (objCode obj) }

    rewriteCode code =
      case code of
        CTMeta v ->
          CTMeta (rewriteTyVar v)
        CTCon ref args ->
          CTCon ref (map rewriteArg args)
        CTLift me inner ->
          CTLift me (rewriteCode inner)

    rewriteArg arg =
      case arg of
        CAObj ty -> CAObj (rewriteObj ty)
        CATm tm -> CATm (rewriteTermDiagram tm)

    rewriteTmVar v =
      let v1 = v { tmvSort = rewriteObj (tmvSort v) }
       in case tmvOwnerMode v1 of
            Just owner ->
              case modeUniverseObj (dModes doc) owner of
                Just universe -> v1 { tmvSort = universe }
                Nothing -> v1
            Nothing -> v1

    rewriteTmMeta v =
      let v1 = v { tmmSort = rewriteObj (tmmSort v) }
       in case tmmOwnerMode v1 of
            Just owner ->
              case modeUniverseObj (dModes doc) owner of
                Just universe -> v1 { tmmSort = universe }
                Nothing -> v1
            Nothing -> v1

    rewriteTyVar v =
      tmVarToObjVar (rewriteTmVar (objVarToTmVar v))

    rewriteInputShape shape =
      case shape of
        InPort ty ->
          InPort (rewriteObj ty)
        InBinder sig ->
          InBinder
            sig
              { bsTmCtx = map rewriteObj (bsTmCtx sig)
              , bsDom = map rewriteObj (bsDom sig)
              , bsCod = map rewriteObj (bsCod sig)
              }

    rewriteGenParam gp =
      case gp of
        GP_Ty v -> GP_Ty (rewriteTmVar v)
        GP_Tm v -> GP_Tm (rewriteTmVar v)

    rewriteGen gd =
      gd
        { gdParams = map rewriteGenParam (gdParams gd)
        , gdDom = map rewriteInputShape (gdDom gd)
        , gdCod = map rewriteObj (gdCod gd)
        }

    rewriteCell cell =
      cell
        { c2Params = map rewriteGenParam (c2Params cell)
        , c2LHS = rewriteDiagram (c2LHS cell)
        , c2RHS = rewriteDiagram (c2RHS cell)
        }

    rewriteAction action =
      action
        { maGenMap = M.map rewriteDiagram (maGenMap action)
        }

    rewriteObligation obl =
      obl
        { obParams = map rewriteGenParam (obParams obl)
        , obDom = map rewriteObj (obDom obl)
        , obCod = map rewriteObj (obCod obl)
        }

    rewriteTermDiagram (TermDiagram diag) =
      TermDiagram (rewriteDiagram diag)

    rewriteDiagram diag =
      diag
        { dTmCtx = map rewriteObj (dTmCtx diag)
        , dPortObj = IM.map rewriteObj (dPortObj diag)
        , dEdges = IM.map rewriteEdge (dEdges diag)
        }

    rewriteEdge edge =
      edge { ePayload = rewritePayload (ePayload edge) }

    rewritePayload payload =
      case payload of
        PGen g attrs bargs ->
          PGen g attrs (map rewriteBinderArg bargs)
        PBox name inner ->
          PBox name (rewriteDiagram inner)
        PFeedback inner ->
          PFeedback (rewriteDiagram inner)
        PSplice mv ->
          PSplice mv
        PTmMeta v ->
          PTmMeta (rewriteTmMeta v)
        PInternalDrop ->
          PInternalDrop

    rewriteBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete (rewriteDiagram inner)
        BAMeta bm -> BAMeta bm

applyPendingClassificationsBestEffort :: BuildOps -> ElabState -> Either Text Doctrine
applyPendingClassificationsBestEffort ops =
  applyPendingClassifications ops True

applyPendingClassificationsFinal :: BuildOps -> ElabState -> Either Text Doctrine
applyPendingClassificationsFinal ops =
  applyPendingClassifications ops False

applyPendingClassifications :: BuildOps -> Bool -> ElabState -> Either Text Doctrine
applyPendingClassifications ops allowSeedFallback st =
  if allowSeedFallback
    then foldM addOne (esDoc st) (esPendingClass st)
    else do
      (doc, errs) <- foldM step (esDoc st, []) (esPendingClass st)
      if null errs
        then Right doc
        else
          Left
            ( "failed to resolve classifiedBy universes:\n"
                <> T.intercalate "\n" errs
            )
  where
    step (doc, errs) pending =
      case addOne doc pending of
        Right doc' -> Right (doc', errs)
        Left err -> Right (doc, errs <> [err])

    addOne doc (mode, rawClass) = do
      ensureMode doc mode
      let classifier = cdrClassifier rawClass
      ensureMode doc classifier
      ctorTables <- deriveCtorTables doc
      universe <-
        case cdrUniverse rawClass of
          UniverseResolved u -> Right u
          UniverseRaw rawUniverse ->
            case boElabUniverseWithTables ops doc ctorTables classifier rawUniverse of
              Right u -> Right u
              Left err ->
                if allowSeedFallback && canKeepSeedUniverse classifier rawUniverse
                  then
                    case M.lookup mode (mtClassifiedBy (dModes doc)) of
                      Just existing -> Right (cdUniverse existing)
                      Nothing ->
                        Left
                          ( "failed to resolve classifiedBy universe for mode "
                              <> renderMode mode
                              <> ": "
                              <> err
                          )
                  else
                    Left
                      ( "failed to resolve classifiedBy universe for mode "
                          <> renderMode mode
                          <> ": "
                          <> err
                      )
      if objOwnerMode universe == classifier
        then Right ()
        else Left "classifiedBy universe mode mismatch"
      let decl =
            ClassificationDecl
              { cdClassifier = classifier
              , cdUniverse = universe
              , cdComp =
                  case M.lookup mode (mtClassifiedBy (dModes doc)) of
                    Just existing -> cdComp existing
                    Nothing -> Nothing
              }
      mt' <-
        case M.lookup mode (mtClassifiedBy (dModes doc)) of
          Nothing ->
            addClassification mode decl (dModes doc)
          Just existing ->
            if cdClassifier existing == classifier
              then
                Right
                  (dModes doc)
                    { mtClassifiedBy = M.insert mode decl (mtClassifiedBy (dModes doc))
                    }
              else Left "classifiedBy classifier mismatch for pending mode"
      let doc' = doc { dModes = mt' }
      Right (materializeResolvedUniverses ops st doc')
      where
        canKeepSeedUniverse classifier0 raw =
          case raw of
            RPTVar _ -> True
            RPTCon ref [] ->
              case rtrMode ref of
                Nothing -> True
                Just q -> ModeName q == classifier0
            _ -> False

applyPendingComprehensions :: ElabState -> Doctrine -> Either Text Doctrine
applyPendingComprehensions st doc0 = do
  ctorTables <- deriveCtorTables doc0
  foldM (addOne ctorTables) doc0 (esPendingComp st)
  where
    addOne ctorTables doc rawComp = do
      let mode = ModeName (rcmpMode rawComp)
      ensureMode doc mode
      classDecl <-
        case M.lookup mode (mtClassifiedBy (dModes doc)) of
          Nothing -> Left "comprehension declaration requires classifiedBy on the mode"
          Just decl -> Right decl
      let ctxExtName = GenName (rcmpCtxExt rawComp)
      let varName = GenName (rcmpVar rawComp)
      let reindexName = GenName (rcmpReindex rawComp)
      ensureGen mode ctxExtName doc
      ensureGen mode varName doc
      ensureGen mode reindexName doc
      ensureNonType ctorTables mode ctxExtName doc
      ensureNonType ctorTables mode varName doc
      ensureNonType ctorTables mode reindexName doc
      let compDecl =
            CompDecl
              { compCtxExt = ctxExtName
              , compVar = varName
              , compReindex = reindexName
              }
      case cdComp classDecl of
        Nothing ->
          let classDecl' = classDecl { cdComp = Just compDecl }
              mt' = (dModes doc) { mtClassifiedBy = M.insert mode classDecl' (mtClassifiedBy (dModes doc)) }
           in Right doc { dModes = mt' }
        Just existing
          | existing == compDecl -> Right doc
          | otherwise -> Left "duplicate comprehension declaration for mode"

    ensureGen mode genName doc =
      case M.lookup mode (dGens doc) >>= M.lookup genName of
        Just _ -> Right ()
        Nothing ->
          Left
            ( "comprehension declaration references unknown generator "
                <> renderModeText mode
                <> "."
                <> renderGenText genName
            )

    ensureNonType ctorTables mode genName doc =
      let isCtor =
            isTypeDeclGenNameInTables
              doc
              ctorTables
              mode
              (ObjName (renderGenText genName))
       in if isCtor
            then
              Left
                ( "comprehension declaration expects term generator but got constructor-like generator "
                    <> renderModeText mode
                    <> "."
                    <> renderGenText genName
                )
            else Right ()

    renderModeText (ModeName n) = n
    renderGenText (GenName n) = n

ensureMode :: Doctrine -> ModeName -> Either Text ()
ensureMode doc mode =
  if M.member mode (mtModes (dModes doc))
    then Right ()
    else Left "unknown mode"

renderMode :: ModeName -> Text
renderMode (ModeName name) = name
