{-# LANGUAGE OverloadedStrings #-}

module Strat.Poly.DiagramInterpretation
  ( DiagramInterpretation(..)
  , interpretDiagram
  , binderHoleNames
  , binderHoleCaptureRiskMetasDiagram
  , stableHoleCaptureRenaming
  , renameBinderArgMetas
  , requirePortType
  , spliceEdge
  , updateEdgePayload
  , applySubstBinderSig
  , applySubstBinderSigs
  , instantiateGenImageBindersWithMapper
  , instantiateGenImageBinders
  ) where

import Control.Monad (foldM)
import qualified Data.List as L
import Data.Text (Text)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T

import Strat.Poly.Diagram
  ( diagramCod
  , diagramDom
  , unionDiagram
  )
import Strat.Poly.Doctrine (BinderSig(..))
import Strat.Poly.Graph
  ( Diagram(..)
  , Edge(..)
  , EdgeId(..)
  , EdgePayload(..)
  , PortId(..)
  , deleteEdgeKeepPorts
  , diagramPortObj
  , mergeBoundaryPairs
  , shiftDiagram
  , validateDiagram
  )
import Strat.Poly.ModeSyntax (ModeName, ModExpr(..))
import Strat.Poly.Syntax
  ( BinderArg(..)
  , BinderMetaVar(..)
  , Obj
  , TmVar(..)
  )
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.Traversal (foldDiagram)
import Strat.Poly.UnifyObj
  ( Subst
  , applySubstCtx
  , applySubstObj
  , emptySubst
  )

data DiagramInterpretation = DiagramInterpretation
  { diMapMode :: ModeName -> Either Text ModeName
  , diMapTmCtxObj :: Obj -> Either Text Obj
  , diMapPortObj :: Obj -> Either Text Obj
  , diMapTmMetaSort :: Obj -> Either Text Obj
  , diMapSplice :: BinderMetaVar -> ModExpr -> Either Text (BinderMetaVar, ModExpr)
  , diOnGenEdge
      :: Diagram
      -> Diagram
      -> Int
      -> Edge
      -> [BinderArg]
      -> Either Text Diagram
  }

interpretDiagram :: DiagramInterpretation -> Diagram -> Either Text Diagram
interpretDiagram interp diagSrc = do
  modeTgt <- diMapMode interp (dMode diagSrc)
  tmCtx' <- mapM (diMapTmCtxObj interp) (dTmCtx diagSrc)
  portObj' <- mapM (diMapPortObj interp) (dPortObj diagSrc)

  let diag0 =
        diagSrc
          { dMode = modeTgt
          , dTmCtx = tmCtx'
          , dPortObj = portObj'
          }

  let edgeKeys = IM.keys (dEdges diagSrc)
  diag1 <- foldM (step diagSrc) diag0 edgeKeys
  validateDiagram diag1
  pure diag1
  where
    step :: Diagram -> Diagram -> Int -> Either Text Diagram
    step src tgt edgeKey = do
      edgeSrc <- requireEdge src edgeKey
      case ePayload edgeSrc of
        PGen _ _ bargsSrc -> do
          bargsMapped <- mapM (mapBinderArg interp) bargsSrc
          diOnGenEdge interp src tgt edgeKey edgeSrc bargsMapped

        PBox nm inner -> do
          inner' <- interpretDiagram interp inner
          updateEdgePayload tgt edgeKey (PBox nm inner')

        PFeedback inner -> do
          inner' <- interpretDiagram interp inner
          updateEdgePayload tgt edgeKey (PFeedback inner')

        PTmMeta v -> do
          sort' <- diMapTmMetaSort interp (tmvSort v)
          updateEdgePayload tgt edgeKey (PTmMeta v { tmvSort = sort' })

        PTmLit lit ->
          updateEdgePayload tgt edgeKey (PTmLit lit)

        PSplice x me -> do
          (x', me') <- diMapSplice interp x me
          updateEdgePayload tgt edgeKey (PSplice x' me')

        PInternalDrop ->
          updateEdgePayload tgt edgeKey PInternalDrop

    requireEdge :: Diagram -> Int -> Either Text Edge
    requireEdge d k =
      case IM.lookup k (dEdges d) of
        Nothing -> Left "interpretDiagram: missing source edge"
        Just e -> Right e

mapBinderArg :: DiagramInterpretation -> BinderArg -> Either Text BinderArg
mapBinderArg interp barg =
  case barg of
    BAMeta x -> Right (BAMeta x)
    BAConcrete d -> BAConcrete <$> interpretDiagram interp d

requirePortType :: Text -> Diagram -> PortId -> Either Text Obj
requirePortType ctx diag p =
  case diagramPortObj diag p of
    Nothing -> Left (ctx <> ": missing port type")
    Just ty -> Right ty

updateEdgePayload :: Diagram -> Int -> EdgePayload -> Either Text Diagram
updateEdgePayload diag edgeKey payload =
  case IM.lookup edgeKey (dEdges diag) of
    Nothing -> Left "updateEdgePayload: missing edge"
    Just edge ->
      let edge' = edge { ePayload = payload }
       in Right diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }

spliceEdge :: Diagram -> Int -> Diagram -> Either Text Diagram
spliceEdge diag edgeKey image = do
  edge <-
    case IM.lookup edgeKey (dEdges diag) of
      Nothing -> Left "spliceEdge: missing edge"
      Just e -> Right e
  let ins = eIns edge
  let outs = eOuts edge
  diag1 <- deleteEdgeKeepPorts diag (EdgeId edgeKey)
  let imageShift = shiftDiagram (dNextPort diag1) (dNextEdge diag1) image
  diag2 <- unionDiagram diag1 imageShift
  let boundary = dIn imageShift <> dOut imageShift
  if length boundary /= length (ins <> outs)
    then Left "spliceEdge: boundary mismatch"
    else do
      diag3 <- mergeBoundaryPairs diag2 (zip (ins <> outs) boundary)
      validateDiagram diag3
      pure diag3

applySubstBinderSig :: TypeTheory -> Subst -> BinderSig -> Either Text BinderSig
applySubstBinderSig tt subst bsig = do
  tmCtx <- applySubstCtx tt subst (bsTmCtx bsig)
  dom <- mapM (applySubstObj tt subst) (bsDom bsig)
  cod <- mapM (applySubstObj tt subst) (bsCod bsig)
  pure bsig { bsTmCtx = tmCtx, bsDom = dom, bsCod = cod }

applySubstBinderSigs
  :: TypeTheory
  -> Subst
  -> M.Map BinderMetaVar BinderSig
  -> Either Text (M.Map BinderMetaVar BinderSig)
applySubstBinderSigs tt subst =
  mapM (applySubstBinderSig tt subst)

binderHoleNames :: Int -> [BinderMetaVar]
binderHoleNames n =
  [ BinderMetaVar ("b" <> T.pack (show i))
  | i <- [0 .. n - 1]
  ]

binderHoleCaptureRiskMetasDiagram :: Diagram -> S.Set BinderMetaVar
binderHoleCaptureRiskMetasDiagram =
  foldDiagram (\_ -> mempty) onPayload (\_ -> mempty)
  where
    onPayload payload =
      case payload of
        PGen _ _ bargs ->
          let holes = S.fromList (binderHoleNames (length bargs))
              edgeMetas = S.fromList [ x | BAMeta x <- bargs ]
           in S.intersection holes edgeMetas
        _ ->
          mempty

stableHoleCaptureRenaming :: S.Set BinderMetaVar -> S.Set BinderMetaVar -> M.Map BinderMetaVar BinderMetaVar
stableHoleCaptureRenaming holeMetas metas =
  let conflicts = L.sort (S.toList (S.intersection holeMetas metas))
      used0 = S.union holeMetas metas
   in freshenBinderMetas used0 conflicts

freshenBinderMetas :: S.Set BinderMetaVar -> [BinderMetaVar] -> M.Map BinderMetaVar BinderMetaVar
freshenBinderMetas used0 conflicts =
  snd (foldl freshenOne (used0, M.empty) conflicts)
  where
    freshenOne (used, renaming) x =
      let x' = pickFreshMeta used x 0
       in (S.insert x' used, M.insert x x' renaming)

    pickFreshMeta used (BinderMetaVar name) n =
      let suffix =
            if n == (0 :: Int)
              then "_arg"
              else "_arg" <> T.pack (show n)
          candidate = BinderMetaVar (name <> suffix)
       in if candidate `S.member` used
            then pickFreshMeta used (BinderMetaVar name) (n + 1)
            else candidate

renameBinderArgMetas :: M.Map BinderMetaVar BinderMetaVar -> [BinderArg] -> [BinderArg]
renameBinderArgMetas renaming =
  map renameOne
  where
    renameOne barg =
      case barg of
        BAConcrete d -> BAConcrete d
        BAMeta x -> BAMeta (M.findWithDefault x x renaming)

data SpliceAction
  = SpliceBindHole Diagram
  | SpliceAlias BinderMetaVar ModExpr

instantiateGenImageBinders
  :: TypeTheory
  -> M.Map BinderMetaVar BinderSig
  -> M.Map BinderMetaVar BinderArg
  -> Diagram
  -> Either Text Diagram
instantiateGenImageBinders tt =
  instantiateGenImageBindersWithMapper tt defaultSpliceMapper


defaultSpliceMapper :: ModExpr -> Diagram -> Either Text Diagram
defaultSpliceMapper me captured =
  if null (mePath me) && meSrc me == dMode captured && meTgt me == dMode captured
    then Right captured
    else Left "instantiateGenImageBinders: splice requires modality-action mapping but no splice mapper is available"

instantiateGenImageBindersWithMapper
  :: TypeTheory
  -> (ModExpr -> Diagram -> Either Text Diagram)
  -> M.Map BinderMetaVar BinderSig
  -> M.Map BinderMetaVar BinderArg
  -> Diagram
  -> Either Text Diagram
instantiateGenImageBindersWithMapper tt mapSplice binderSigs holeSub diag0 = do
  diag1 <- recurseDiagram diag0
  expandSplicesLoop diag1
  where
    recurseDiagram diag = do
      edges' <- traverse recurseEdge (dEdges diag)
      pure diag { dEdges = edges' }

    recurseEdge edge =
      case ePayload edge of
        PGen g args bargs -> do
          bargs' <- mapM recurseBinderArg bargs
          pure edge { ePayload = PGen g args bargs' }
        PBox name inner -> do
          inner' <- instantiateGenImageBindersWithMapper tt mapSplice binderSigs holeSub inner
          pure edge { ePayload = PBox name inner' }
        PFeedback inner -> do
          inner' <- instantiateGenImageBindersWithMapper tt mapSplice binderSigs holeSub inner
          pure edge { ePayload = PFeedback inner' }
        PSplice x me ->
          pure edge { ePayload = PSplice x me }
        PTmMeta v ->
          pure edge { ePayload = PTmMeta v }
        PTmLit lit ->
          pure edge { ePayload = PTmLit lit }
        PInternalDrop ->
          pure edge { ePayload = PInternalDrop }
      where
        recurseBinderArg barg =
          case barg of
            BAConcrete inner ->
              BAConcrete <$> instantiateGenImageBindersWithMapper tt mapSplice binderSigs holeSub inner
            BAMeta x ->
              case M.lookup x holeSub of
                Nothing ->
                  if M.member x binderSigs
                    then Left "instantiateGenImageBinders: missing binder-hole substitution"
                    else Right (BAMeta x)
                Just mapped ->
                  case mapped of
                    BAConcrete d -> do
                      checkConcreteAgainstSig x d
                      Right (BAConcrete d)
                    BAMeta y ->
                      Right (BAMeta y)

    expandSplicesLoop diag = do
      mNext <- findExpandableSplice diag
      case mNext of
        Nothing -> Right diag
        Just (edgeKey, action) ->
          case action of
            SpliceAlias x' me -> do
              diag' <- updateEdgePayload diag edgeKey (PSplice x' me)
              expandSplicesLoop diag'
            SpliceBindHole dMapped -> do
              edge <- requireEdge diag edgeKey
              checkSpliceInsertion diag edge dMapped
              diag' <- spliceEdge diag edgeKey dMapped
              expandSplicesLoop diag'

    findExpandableSplice diag =
      go (IM.toAscList (dEdges diag))
      where
        go [] = Right Nothing
        go ((edgeKey, edge):rest) =
          case ePayload edge of
            PSplice hole me -> do
              resolved <- resolveSpliceHole hole
              case resolved of
                BAMeta x'
                  | x' /= hole -> Right (Just (edgeKey, SpliceAlias x' me))
                  | otherwise -> go rest
                BAConcrete d -> do
                  checkConcreteAgainstSig hole d
                  dMapped <- mapSpliceForHole me d
                  checkSpliceInsertion diag edge dMapped
                  Right (Just (edgeKey, SpliceBindHole dMapped))
            _ -> go rest

    requireEdge diag edgeKey =
      case IM.lookup edgeKey (dEdges diag) of
        Nothing -> Left "instantiateGenImageBinders: internal error: missing edge"
        Just edge -> Right edge

    resolveSpliceHole x = resolveAliasChain S.empty [] x

    resolveAliasChain seen chain x
      | x `S.member` seen =
          Left ("instantiateGenImageBinders: binder-hole alias cycle: " <> renderAliasCycle (reverse (x : chain)))
      | otherwise =
          case M.lookup x holeSub of
            Nothing ->
              if M.member x binderSigs
                then Left "instantiateGenImageBinders: missing binder-hole substitution"
                else Right (BAMeta x)
            Just (BAConcrete d) ->
              Right (BAConcrete d)
            Just (BAMeta y) ->
              if M.member y holeSub
                then resolveAliasChain (S.insert x seen) (x : chain) y
                else
                  if M.member y binderSigs
                    then Left "instantiateGenImageBinders: missing binder-hole substitution"
                    else Right (BAMeta y)

    mapSpliceForHole me d = do
      if dMode d == meSrc me
        then Right ()
        else Left "instantiateGenImageBinders: splice mapper source-mode mismatch"
      dMapped <-
        if null (mePath me)
          then Right d
          else mapSplice me d
      if dMode dMapped == meTgt me
        then Right dMapped
        else Left "instantiateGenImageBinders: splice mapper target-mode mismatch"

    checkSpliceInsertion diag edge d = do
      if dMode d == dMode diag
        then Right ()
        else Left "instantiateGenImageBinders: splice insertion mode mismatch"
      tmCaptured <- applySubstCtx tt emptySubst (dTmCtx d)
      tmHost <- applySubstCtx tt emptySubst (dTmCtx diag)
      if tmCaptured == tmHost
        then Right ()
        else Left "instantiateGenImageBinders: splice insertion term-context mismatch"
      if length (dIn d) == length (eIns edge) && length (dOut d) == length (eOuts edge)
        then Right ()
        else Left "instantiateGenImageBinders: splice insertion boundary arity mismatch"
      domSplice <- mapM (requirePortType "instantiateGenImageBinders" diag) (eIns edge)
      codSplice <- mapM (requirePortType "instantiateGenImageBinders" diag) (eOuts edge)
      domCaptured <- mapM (requirePortType "instantiateGenImageBinders" d) (dIn d)
      codCaptured <- mapM (requirePortType "instantiateGenImageBinders" d) (dOut d)
      if domSplice == domCaptured && codSplice == codCaptured
        then Right ()
        else Left "instantiateGenImageBinders: splice insertion boundary mismatch"

    checkConcreteAgainstSig hole d =
      case M.lookup hole binderSigs of
        Nothing -> Right ()
        Just sig -> do
          sigTm <- applySubstCtx tt emptySubst (bsTmCtx sig)
          dTm <- applySubstCtx tt emptySubst (dTmCtx d)
          if dTm == sigTm
            then Right ()
            else Left "instantiateGenImageBinders: binder argument term-context mismatch"
          dDom <- diagramDom d
          dCod <- diagramCod d
          dDom' <- applySubstCtx tt emptySubst dDom
          dCod' <- applySubstCtx tt emptySubst dCod
          sigDom <- applySubstCtx tt emptySubst (bsDom sig)
          sigCod <- applySubstCtx tt emptySubst (bsCod sig)
          if dDom' == sigDom && dCod' == sigCod
            then Right ()
            else Left "instantiateGenImageBinders: binder argument boundary mismatch"

    renderAliasCycle xs =
      T.intercalate " -> " (map renderMeta xs)

    renderMeta (BinderMetaVar name) = "?" <> name
