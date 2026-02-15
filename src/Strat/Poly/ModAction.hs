{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ModAction
  ( applyModExpr
  , applyAction
  , validateActionSemantics
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Strat.Common.Rules (RewritePolicy(..))
import Strat.Poly.Attr (AttrMap, AttrSubst, AttrVar(..), AttrTerm(..))
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Doctrine
import Strat.Poly.Graph
import Strat.Poly.Diagram
import Strat.Poly.Morphism (instantiateGenImageBinders)
import Strat.Poly.ModeTheory
import Strat.Poly.Normalize (joinableWithin)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Rewrite (rulesFromPolicy)
import Strat.Poly.TypeExpr
import Strat.Poly.UnifyTy
import Strat.Poly.TypeTheory

validateActionSemantics :: Doctrine -> Either Text ()
validateActionSemantics doc = do
  mapM_ checkRulePreservation (M.toList (dActions doc))
  mapM_ checkModEqn (mtEqns (dModes doc))
  where
    tt = doctrineTypeTheory doc

    checkRulePreservation (modName, action) = do
      decl <-
        case M.lookup modName (mtDecls (dModes doc)) of
          Nothing -> Left "validateDoctrine: action references unknown modality"
          Just d -> Right d
      let srcMode = mdSrc decl
      let srcRules = [ c | c <- dCells2 doc, dMode (c2LHS c) == srcMode ]
      let rules = rulesFromPolicy (maPolicy action) (dCells2 doc)
      mapM_ (checkOneRule modName action rules) srcRules

    checkOneRule modName action rules cell = do
      cell' <- freshenRuleTyVars tt cell
      lhs <- applyAction doc modName (c2LHS cell')
      rhs <- applyAction doc modName (c2RHS cell')
      ok <- joinableWithin tt (maFuel action) rules lhs rhs
      if ok
        then Right ()
        else Left ("validateDoctrine: action does not preserve rule " <> c2Name cell)

    checkModEqn eqn = do
      let lhs = meLHS eqn
      let rhs = meRHS eqn
      let mods = mePath lhs <> mePath rhs
      if all (`M.member` dActions doc) mods
        then do
          let srcMode = meSrc lhs
          let gens = M.elems (M.findWithDefault M.empty srcMode (dGens doc))
          let fuel = maximum (50 : [ maFuel action | m <- mods, action <- maybeToList (M.lookup m (dActions doc)) ])
          let policy = choosePolicy mods
          let rules = rulesFromPolicy policy (dCells2 doc)
          mapM_ (checkOneGen lhs rhs fuel rules) gens
        else Right ()

    checkOneGen lhs rhs fuel rules gd = do
      gDiag <- genericGenDiagram gd
      lhsMapped <- applyModExpr doc lhs gDiag
      rhsMapped <- applyModExpr doc rhs gDiag
      ok <- joinableWithin tt fuel rules lhsMapped rhsMapped
      if ok
        then Right ()
        else Left ("validateDoctrine: action coherence failed for modality equation on generator " <> renderGenName (gdName gd))

    choosePolicy mods =
      let policies = [ maPolicy action | m <- mods, action <- maybeToList (M.lookup m (dActions doc)) ]
       in case policies of
            [] -> UseStructuralAsBidirectional
            (p:ps) ->
              if all (== p) ps
                then p
                else UseStructuralAsBidirectional

freshenRuleTyVars :: TypeTheory -> Cell2 -> Either Text Cell2
freshenRuleTyVars tt cell = do
  let vars = c2TyVars cell
  if null vars
    then Right cell
    else do
      let used0 =
            S.fromList
              [ (tvMode v, tvName v)
              | v <- S.toList (S.union (freeTyVarsDiagram (c2LHS cell)) (freeTyVarsDiagram (c2RHS cell)))
              ]
      let (substMap, _used) = foldl freshOne (M.empty, used0) vars
      let subst = emptySubst { sTy = substMap }
      lhs <- applySubstDiagram tt subst (c2LHS cell)
      rhs <- applySubstDiagram tt subst (c2RHS cell)
      pure cell { c2LHS = lhs, c2RHS = rhs }
  where
    freshOne (acc, used) v =
      let name' = pickFresh used (tvMode v) ("actchk_" <> tvName v) 0
          v' = v { tvName = name' }
          used' = S.insert (tvMode v', tvName v') used
          acc' = M.insert v (TVar v') acc
       in (acc', used')

    pickFresh used mode base n =
      let suffix = if n == (0 :: Int) then "" else T.pack (show n)
          candidate = base <> suffix
       in if (mode, candidate) `S.member` used
            then pickFresh used mode base (n + 1)
            else candidate

maybeToList :: Maybe a -> [a]
maybeToList mv =
  case mv of
    Nothing -> []
    Just x -> [x]

renderGenName :: GenName -> Text
renderGenName (GenName g) = g

applyModExpr :: Doctrine -> ModExpr -> Diagram -> Either Text Diagram
applyModExpr doc me diag = do
  if dMode diag /= meSrc me
    then Left "map: source mode mismatch"
    else pure ()
  case mePath me of
    [] ->
      if meSrc me == meTgt me
        then Right diag
        else Left "map: empty modality path has mismatched endpoints"
    ms -> do
      out <- foldM (\d m -> applyAction doc m d) diag ms
      if dMode out == meTgt me
        then Right out
        else Left "map: result mode mismatch"

applyAction :: Doctrine -> ModName -> Diagram -> Either Text Diagram
applyAction doc mName diagSrc = do
  decl <-
    case M.lookup mName (mtDecls (dModes doc)) of
      Nothing -> Left "map: unknown modality"
      Just d -> Right d
  action <-
    case M.lookup mName (dActions doc) of
      Nothing -> Left "map: missing action declaration"
      Just a -> Right a
  if dMode diagSrc /= mdSrc decl
    then Left "map: modality source mismatch"
    else pure ()
  let me = ModExpr { meSrc = mdSrc decl, meTgt = mdTgt decl, mePath = [mName] }
  dTmCtx' <- mapM (mapTypeIfSource me) (dTmCtx diagSrc)
  dPortTy' <- mapM (mapType me) (dPortTy diagSrc)
  let diag0 = diagSrc { dMode = mdTgt decl, dTmCtx = dTmCtx', dPortTy = dPortTy' }
  let edgeKeys = IM.keys (dEdges diagSrc)
  diag1 <- foldM (step action me) diag0 edgeKeys
  validateDiagram diag1
  pure diag1
  where
    tt = doctrineTypeTheory doc

    mapType me ty = do
      if typeMode ty /= meSrc me
        then Left "map: type mode does not match action source"
        else normalizeTypeExpr (dModes doc) (TMod me ty)

    mapTypeIfSource me ty =
      if typeMode ty == meSrc me
        then mapType me ty
        else pure ty

    step action me diagTgt edgeKey = do
      edgeSrc <-
        case IM.lookup edgeKey (dEdges diagSrc) of
          Nothing -> Left "map: missing source edge"
          Just e -> Right e
      case ePayload edgeSrc of
        PGen g attrs bargs -> do
          genDecl <- lookupSrcGen doc (dMode diagSrc) g
          mappedBargs <- mapM (mapBinderArg mName) bargs
          img0raw <-
            case M.lookup (dMode diagSrc, g) (maGenMap action) of
              Nothing -> Left "map: missing generator image"
              Just d -> Right d
          img0 <- freshenImageTyVars tt diagTgt img0raw
          (img1, subst) <- instantiateImage tt diagTgt edgeKey img0
          let img2 = applyAttrSubstDiagram (actionAttrSubst genDecl attrs) img1
          img3 <- instantiateMappedBinders tt me genDecl mappedBargs subst img2
          img4 <- weakenDiagramTmCtxTo (dTmCtx diagTgt) img3
          spliceEdge diagTgt edgeKey img4
        PBox name inner -> do
          inner' <- applyAction doc mName inner
          updateEdgePayload diagTgt edgeKey (PBox name inner')
        PFeedback inner -> do
          inner' <- applyAction doc mName inner
          updateEdgePayload diagTgt edgeKey (PFeedback inner')
        PSplice x ->
          updateEdgePayload diagTgt edgeKey (PSplice x)
        PTmMeta v -> do
          sort' <- mapTypeIfSource me (tmvSort v)
          updateEdgePayload diagTgt edgeKey (PTmMeta v { tmvSort = sort' })
        PInternalDrop ->
          updateEdgePayload diagTgt edgeKey PInternalDrop

    mapBinderArg modName barg =
      case barg of
        BAConcrete inner ->
          BAConcrete <$> applyAction doc modName inner
        BAMeta x ->
          Right (BAMeta x)

    instantiateMappedBinders typeTheory me genDecl mappedBargs subst image = do
      let slots = [ bs | InBinder bs <- gdDom genDecl ]
      if length slots /= length mappedBargs
        then Left "map: source binder argument arity mismatch"
        else Right ()
      let holes = [ BinderMetaVar ("b" <> T.pack (show i)) | i <- [0 :: Int .. length slots - 1] ]
      sigs0 <- mapM mapBinderSig (M.fromList (zip holes slots))
      sigs <- applySubstBinderSigs typeTheory subst sigs0
      let holeSub = M.fromList (zip holes mappedBargs)
      out <- instantiateGenImageBinders typeTheory sigs holeSub image
      let remaining = S.intersection (M.keysSet sigs) (binderMetaVarsDiagram out)
      if S.null remaining
        then Right out
        else Left "map: uninstantiated binder holes in action image"
      where
        mapBinderSig sig = do
          tmCtx <- mapM (mapTypeIfSource me) (bsTmCtx sig)
          dom <- mapM (mapType me) (bsDom sig)
          cod <- mapM (mapType me) (bsCod sig)
          pure sig { bsTmCtx = tmCtx, bsDom = dom, bsCod = cod }

    freshenImageTyVars typeTheory host image = do
      let vars = S.toList (freeTyVarsDiagram image)
      if null vars
        then Right image
        else do
          let used0 = S.fromList [ (tvMode v, tvName v) | v <- S.toList (freeTyVarsDiagram host) ]
          let (_, pairsRev) = foldl freshOne (used0, []) vars
          let subst = emptySubst { sTy = M.fromList (reverse pairsRev) }
          applySubstDiagram typeTheory subst image
      where
        freshOne (used, acc) v =
          let name' = pickFresh used (tvMode v) (tvName v <> "_img") 0
              v' = v { tvName = name' }
              used' = S.insert (tvMode v', tvName v') used
           in (used', (v, TVar v') : acc)

        pickFresh used mode base n =
          let suffix = if n == (0 :: Int) then "" else T.pack (show n)
              candidate = base <> suffix
           in if (mode, candidate) `S.member` used
                then pickFresh used mode base (n + 1)
                else candidate

genericGenDiagram :: GenDecl -> Either Text Diagram
genericGenDiagram gd = do
  let mode = gdMode gd
  let attrs = M.fromList [ (fieldName, ATVar (AttrVar fieldName sortName)) | (fieldName, sortName) <- gdAttrs gd ]
  let binderSlots = [ bs | InBinder bs <- gdDom gd ]
  let bargs = [ BAMeta (BinderMetaVar ("b" <> T.pack (show i))) | i <- [0 :: Int .. length binderSlots - 1] ]
  let (ins, d0) = allocPorts (gdPlainDom gd) (emptyDiagram mode [])
  let (outs, d1) = allocPorts (gdCod gd) d0
  d2 <- addEdgePayload (PGen (gdName gd) attrs bargs) ins outs d1
  let d3 = d2 { dIn = ins, dOut = outs }
  validateDiagram d3
  pure d3
  where
    allocPorts [] diag = ([], diag)
    allocPorts (ty:rest) diag =
      let (pid, diag1) = freshPort ty diag
          (pids, diag2) = allocPorts rest diag1
       in (pid : pids, diag2)

actionAttrSubst :: GenDecl -> AttrMap -> AttrSubst
actionAttrSubst genDecl attrs =
  M.fromList
    [ (AttrVar fieldName sortName, M.findWithDefault (ATVar (AttrVar fieldName sortName)) fieldName attrs)
    | (fieldName, sortName) <- gdAttrs genDecl
    ]

applySubstBinderSigs :: TypeTheory -> Subst -> M.Map BinderMetaVar BinderSig -> Either Text (M.Map BinderMetaVar BinderSig)
applySubstBinderSigs tt subst =
  mapM (applySubstBinderSig tt subst)

applySubstBinderSig :: TypeTheory -> Subst -> BinderSig -> Either Text BinderSig
applySubstBinderSig tt subst sig = do
  tmCtx <- applySubstCtx tt subst (bsTmCtx sig)
  dom <- applySubstCtx tt subst (bsDom sig)
  cod <- applySubstCtx tt subst (bsCod sig)
  pure sig { bsTmCtx = tmCtx, bsDom = dom, bsCod = cod }

lookupSrcGen :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupSrcGen doc mode genName =
  case M.lookup mode (dGens doc) >>= M.lookup genName of
    Nothing -> Left "map: unknown source generator"
    Just gd -> Right gd

instantiateImage :: TypeTheory -> Diagram -> Int -> Diagram -> Either Text (Diagram, Subst)
instantiateImage tt diag edgeKey img = do
  edge <-
    case IM.lookup edgeKey (dEdges diag) of
      Nothing -> Left "map: missing target edge"
      Just e -> Right e
  domEdge <- mapM (requirePortType diag) (eIns edge)
  codEdge <- mapM (requirePortType diag) (eOuts edge)
  domImg <- diagramDom img
  codImg <- diagramCod img
  let flexTy = freeTyVarsDiagram img
  let flexTm = freeTmVarsDiagram img
  sDom <- unifyCtxDiagram tt diag flexTy flexTm domImg domEdge
  codImg1 <- applySubstCtx tt sDom codImg
  codEdge1 <- applySubstCtx tt sDom codEdge
  sCod <- unifyCtxDiagram tt diag flexTy flexTm codImg1 codEdge1
  s <- composeSubst tt sCod sDom
  img' <- applySubstDiagram tt s img
  pure (img', s)

requirePortType :: Diagram -> PortId -> Either Text TypeExpr
requirePortType diag pid =
  case diagramPortType diag pid of
    Nothing -> Left "map: missing port type"
    Just ty -> Right ty

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

updateEdgePayload :: Diagram -> Int -> EdgePayload -> Either Text Diagram
updateEdgePayload diag edgeKey payload =
  case IM.lookup edgeKey (dEdges diag) of
    Nothing -> Left "updateEdgePayload: missing edge"
    Just edge ->
      let edge' = edge { ePayload = payload }
      in Right diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
