{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ModAction
  ( applyModExpr
  , mapTypeByModExpr
  , applyAction
  , ActionSemanticsResult(..)
  , validateActionSemanticsWithBudgetResult
  , validateActionSemanticsWithBudget
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
import Strat.Poly.Cell2 (Cell2(..), c2TyVars)
import Strat.Poly.Doctrine
import Strat.Poly.Graph
import Strat.Poly.Diagram
import Strat.Poly.DiagramInterpretation
  ( DiagramInterpretation(..)
  , applySubstBinderSigs
  , binderHoleNames
  , instantiateGenImageBinders
  , interpretDiagram
  , requirePortType
  , spliceEdge
  )
import Strat.Poly.ModeTheory
import Strat.Poly.Normalize (autoJoinProof)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Proof
  ( JoinProof
  , SearchBudget
  , SearchLimit
  , SearchOutcome(..)
  , defaultSearchBudget
  , renderSearchLimit
  , checkJoinProof
  )
import Strat.Poly.Rewrite (rulesFromPolicy)
import Strat.Poly.Obj
import Strat.Poly.UnifyObj hiding (applySubstDiagram)
import Strat.Poly.TypeTheory

data ActionSemanticsResult
  = ActionSemanticsProved [(Text, JoinProof)]
  | ActionSemanticsUndecided Text SearchLimit
  deriving (Eq, Show)

validateActionSemanticsWithBudgetResult :: SearchBudget -> Doctrine -> Either Text ActionSemanticsResult
validateActionSemanticsWithBudgetResult budget doc = do
  tt <- doctrineTypeTheory doc
  let ctorTables = ttCtorTablesByOwner tt
  actionResult <- checkActions tt ctorTables (M.toList (dActions doc))
  case actionResult of
    ActionSemanticsUndecided{} ->
      Right actionResult
    ActionSemanticsProved actionProofs -> do
      eqnResult <- checkEqns tt ctorTables (mtEqns (dModes doc))
      case eqnResult of
        ActionSemanticsUndecided{} ->
          Right eqnResult
        ActionSemanticsProved eqnProofs ->
          Right (ActionSemanticsProved (actionProofs <> eqnProofs))
  where
    checkActions _ _ [] = Right (ActionSemanticsProved [])
    checkActions tt ctorTables (decl:rest) = do
      result <- checkRulePreservation tt decl
      case result of
        ActionSemanticsUndecided{} -> Right result
        ActionSemanticsProved proofs -> do
          restResult <- checkActions tt ctorTables rest
          case restResult of
            ActionSemanticsUndecided{} -> Right restResult
            ActionSemanticsProved restProofs ->
              Right (ActionSemanticsProved (proofs <> restProofs))

    checkEqns _ _ [] = Right (ActionSemanticsProved [])
    checkEqns tt ctorTables (eqn:rest) = do
      result <- checkModEqn tt ctorTables eqn
      case result of
        ActionSemanticsUndecided{} -> Right result
        ActionSemanticsProved proofs -> do
          restResult <- checkEqns tt ctorTables rest
          case restResult of
            ActionSemanticsUndecided{} -> Right restResult
            ActionSemanticsProved restProofs ->
              Right (ActionSemanticsProved (proofs <> restProofs))

    checkRulePreservation tt (modName, action) = do
      decl <-
        case M.lookup modName (mtDecls (dModes doc)) of
          Nothing -> Left "validateDoctrine: action references unknown modality"
          Just d -> Right d
      let srcMode = mdSrc decl
      let srcRules = [ c | c <- dCells2 doc, dMode (c2LHS c) == srcMode ]
      let rules = rulesFromPolicy (maPolicy action) (dCells2 doc)
      checkRules tt modName rules srcRules

    checkRules _ _ _ [] = Right (ActionSemanticsProved [])
    checkRules tt modName rules (cell:rest) = do
      result <- checkOneRule tt modName rules cell
      case result of
        ActionSemanticsUndecided{} -> Right result
        ActionSemanticsProved proofs -> do
          restResult <- checkRules tt modName rules rest
          case restResult of
            ActionSemanticsUndecided{} -> Right restResult
            ActionSemanticsProved restProofs ->
              Right (ActionSemanticsProved (proofs <> restProofs))

    checkOneRule tt modName rules cell = do
      cell' <- freshenRuleTyVars tt cell
      lhs <- applyAction doc modName (c2LHS cell')
      rhs <- applyAction doc modName (c2RHS cell')
      proof <- autoJoinProof tt budget rules lhs rhs
      case proof of
        SearchUndecided lim ->
          Right
            ( ActionSemanticsUndecided
                ("rule " <> c2Name cell)
                lim
            )
        SearchProved witness -> do
          checkJoinProof tt rules witness
          Right (ActionSemanticsProved [("rule " <> c2Name cell, witness)])

    checkModEqn tt ctorTables eqn = do
      let lhs = meLHS eqn
      let rhs = meRHS eqn
      let mods = mePath lhs <> mePath rhs
      if all (`M.member` dActions doc) mods
        then do
          let srcMode = meSrc lhs
          let gens =
                [ gd
                | gd <- M.elems (M.findWithDefault M.empty srcMode (dGens doc))
                , not (isTypeDeclGenNameInTables doc ctorTables srcMode (ObjName (renderGenName (gdName gd))))
                ]
          let policy = choosePolicy mods
          let rules = rulesFromPolicy policy (dCells2 doc)
          checkGens tt lhs rhs rules gens
        else Right (ActionSemanticsProved [])

    checkGens _ _ _ _ [] = Right (ActionSemanticsProved [])
    checkGens tt lhs rhs rules (gd:rest) = do
      result <- checkOneGen tt lhs rhs rules gd
      case result of
        ActionSemanticsUndecided{} -> Right result
        ActionSemanticsProved proofs -> do
          restResult <- checkGens tt lhs rhs rules rest
          case restResult of
            ActionSemanticsUndecided{} -> Right restResult
            ActionSemanticsProved restProofs ->
              Right (ActionSemanticsProved (proofs <> restProofs))

    checkOneGen tt lhs rhs rules gd = do
      gDiag <- genericGenDiagram gd
      lhsMapped <- applyModExpr doc lhs gDiag
      rhsMapped <- applyModExpr doc rhs gDiag
      proof <- autoJoinProof tt budget rules lhsMapped rhsMapped
      case proof of
        SearchUndecided lim ->
          Right
            ( ActionSemanticsUndecided
                ("generator " <> renderGenName (gdName gd))
                lim
            )
        SearchProved witness -> do
          checkJoinProof tt rules witness
          Right (ActionSemanticsProved [("generator " <> renderGenName (gdName gd), witness)])

    choosePolicy mods =
      let policies = [ maPolicy action | m <- mods, action <- maybeToList (M.lookup m (dActions doc)) ]
       in case policies of
            [] -> UseStructuralAsBidirectional
            (p:ps) ->
              if all (== p) ps
                then p
                else UseStructuralAsBidirectional

validateActionSemantics :: Doctrine -> Either Text ()
validateActionSemantics = validateActionSemanticsWithBudget defaultSearchBudget

validateActionSemanticsWithBudget :: SearchBudget -> Doctrine -> Either Text ()
validateActionSemanticsWithBudget budget doc = do
  result <- validateActionSemanticsWithBudgetResult budget doc
  case result of
    ActionSemanticsProved _ ->
      Right ()
    ActionSemanticsUndecided label lim ->
      Left
        ( "validateDoctrine: action semantics undecided for "
            <> label
            <> " ("
            <> renderSearchLimit lim
            <> ")"
        )

freshenRuleTyVars :: TypeTheory -> Cell2 -> Either Text Cell2
freshenRuleTyVars tt cell = do
  let vars = c2TyVars cell
  if null vars
    then Right cell
    else do
      let used0 =
            S.fromList
              [ (ovMode v, ovName v)
              | v <- S.toList (S.union (freeObjVarsDiagram (c2LHS cell)) (freeObjVarsDiagram (c2RHS cell)))
              ]
      let (substMap, _used) = foldl freshOne (M.empty, used0) vars
      let subst = mkSubst substMap M.empty
      lhs <- applySubstDiagram tt subst (c2LHS cell)
      rhs <- applySubstDiagram tt subst (c2RHS cell)
      pure cell { c2LHS = lhs, c2RHS = rhs }
  where
    freshOne (acc, used) v =
          let name' = pickFresh used (tyVarMode v) ("actchk_" <> tmvName v) 0
              v' = v { tmvName = name' }
              used' = S.insert (tyVarMode v', tmvName v') used
              acc' = M.insert (tmVarToObjVar v) (OVar (tmVarToObjVar v')) acc
           in (acc', used')

    tyVarMode v =
      case tmvOwnerMode v of
        Just m -> m
        Nothing -> objOwnerMode (tmvSort v)

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

mapTypeByModExpr :: Doctrine -> ModExpr -> Obj -> Either Text Obj
mapTypeByModExpr doc me ty = do
  codeLift <- classifierLiftForModExpr (dModes doc) me
  mapTypeWithLift (dModes doc) me codeLift ty

mapTypeWithLift :: ModeTheory -> ModExpr -> ModExpr -> Obj -> Either Text Obj
mapTypeWithLift mt me codeLift ty = do
  if objOwnerMode ty /= meSrc me
    then Left "map: type mode does not match action source"
    else
      normalizeObjExpr
        mt
        Obj
          { objOwnerMode = meTgt me
          , objCode = CTLift codeLift (objCode ty)
          }

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
  tt <- doctrineTypeTheory doc
  let me = ModExpr { meSrc = mdSrc decl, meTgt = mdTgt decl, mePath = [mName] }
  codeLift <- classifierLiftForModExpr (dModes doc) me
  let interp =
        DiagramInterpretation
          { diMapMode = \m ->
              if m == mdSrc decl then Right (mdTgt decl)
              else Left "map: modality source mismatch"
          , diMapTmCtxObj = mapTypeIfSource me codeLift
          , diMapPortObj = mapType me codeLift
          , diMapTmMetaSort = mapTypeIfSource me codeLift
          , diOnGenEdge = onGenEdge tt action me codeLift
          }
  interpretDiagram interp diagSrc
  where
    mapType me codeLift = mapTypeWithLift (dModes doc) me codeLift

    mapTypeIfSource me codeLift ty =
      if objOwnerMode ty == meSrc me
        then mapType me codeLift ty
        else pure ty

    onGenEdge tt action me codeLift diagSrc0 diagTgt edgeKey edgeSrc mappedBargs =
      case ePayload edgeSrc of
        PGen g attrs _bargsSrc -> do
          genDecl <- lookupGenDeclInDoctrine "map: unknown source generator" doc (dMode diagSrc0) g
          img0raw <-
            case M.lookup (dMode diagSrc0, g) (maGenMap action) of
              Nothing -> Left "map: missing generator image"
              Just d -> Right d
          img0 <- freshenImageTyVars tt diagTgt img0raw
          (img1, subst) <- instantiateImage tt diagTgt edgeKey img0
          let img2 = applyAttrSubstDiagram (actionAttrSubst genDecl attrs) img1
          img3 <- instantiateMappedBinders tt me codeLift genDecl mappedBargs subst img2
          img4 <- weakenDiagramTmCtxTo (dTmCtx diagTgt) img3
          diagTgtNorm <- normalizeBoundaryPorts (eIns edgeSrc <> eOuts edgeSrc) diagTgt
          img4Norm <- normalizeDiagramObjExprs (dModes doc) img4
          spliceEdge diagTgtNorm edgeKey img4Norm
        _ ->
          Left "map: internal error: diOnGenEdge called on non-PGen"

    instantiateMappedBinders typeTheory me codeLift genDecl mappedBargs subst image = do
      let slots = [ bs | InBinder bs <- gdDom genDecl ]
      if length slots /= length mappedBargs
        then Left "map: source binder argument arity mismatch"
        else Right ()
      let holes = binderHoleNames (length slots)
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
          tmCtx <- mapM (mapTypeIfSource me codeLift) (bsTmCtx sig)
          dom <- mapM (mapType me codeLift) (bsDom sig)
          cod <- mapM (mapType me codeLift) (bsCod sig)
          pure sig { bsTmCtx = tmCtx, bsDom = dom, bsCod = cod }

    freshenImageTyVars typeTheory host image = do
      let vars = map objVarToTmVar (S.toList (freeObjVarsDiagram image))
      if null vars
        then Right image
        else do
          let used0 = S.fromList [ (ovMode v, ovName v) | v <- S.toList (freeObjVarsDiagram host) ]
          let (_, pairsRev) = foldl freshOne (used0, []) vars
          let subst = mkSubst (M.fromList (reverse pairsRev)) M.empty
          applySubstDiagram typeTheory subst image
      where
        freshOne (used, acc) v =
          let name' = pickFresh used (tyVarMode v) (tmvName v <> "_img") 0
              v' = v { tmvName = name' }
              used' = S.insert (tyVarMode v', tmvName v') used
           in (used', (tmVarToObjVar v, OVar (tmVarToObjVar v')) : acc)

        tyVarMode v =
          case tmvOwnerMode v of
            Just m -> m
            Nothing -> objOwnerMode (tmvSort v)

        pickFresh used mode base n =
          let suffix = if n == (0 :: Int) then "" else T.pack (show n)
              candidate = base <> suffix
           in if (mode, candidate) `S.member` used
                then pickFresh used mode base (n + 1)
                else candidate

    normalizeBoundaryPorts pids diag = do
      portObj' <- foldM normalizeOne (dPortObj diag) pids
      pure diag { dPortObj = portObj' }
      where
        normalizeOne mp pid =
          case IM.lookup (unPortId pid) mp of
            Nothing -> Left "map: missing boundary port while normalizing action image splice"
            Just ty -> do
              ty' <- normalizeObjExpr (dModes doc) ty
              pure (IM.insert (unPortId pid) ty' mp)

genericGenDiagram :: GenDecl -> Either Text Diagram
genericGenDiagram gd = do
  let mode = gdMode gd
  let attrs = M.fromList [ (fieldName, ATVar (AttrVar fieldName sortName)) | (fieldName, sortName) <- gdAttrs gd ]
  let binderSlots = [ bs | InBinder bs <- gdDom gd ]
  let bargs = map BAMeta (binderHoleNames (length binderSlots))
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

instantiateImage :: TypeTheory -> Diagram -> Int -> Diagram -> Either Text (Diagram, Subst)
instantiateImage tt diag edgeKey img = do
  edge <-
    case IM.lookup edgeKey (dEdges diag) of
      Nothing -> Left "map: missing target edge"
      Just e -> Right e
  domEdge <- mapM (requirePortType "map" diag) (eIns edge)
  codEdge <- mapM (requirePortType "map" diag) (eOuts edge)
  domImg <- diagramDom img
  codImg <- diagramCod img
  let flexTy = S.map objVarToTmVar (freeObjVarsDiagram img)
  let flexTm = freeTmVarsDiagram img
  let flex = S.union flexTy flexTm
  sDom <- unifyCtxDiagram tt diag flex domImg domEdge
  codImg1 <- applySubstCtx tt sDom codImg
  codEdge1 <- applySubstCtx tt sDom codEdge
  sCod <- unifyCtxDiagram tt diag flex codImg1 codEdge1
  s <- composeSubst tt sCod sDom
  img' <- applySubstDiagram tt s img
  imgNorm <- normalizeDiagramObjExprs (ttModes tt) img'
  pure (imgNorm, s)

normalizeDiagramObjExprs :: ModeTheory -> Diagram -> Either Text Diagram
normalizeDiagramObjExprs mt diag = do
  portObj' <- mapM (normalizeObjExpr mt) (dPortObj diag)
  tmCtx' <- mapM (normalizeObjExpr mt) (dTmCtx diag)
  edges' <- mapM normalizeEdge (dEdges diag)
  pure diag { dPortObj = portObj', dTmCtx = tmCtx', dEdges = edges' }
  where
    normalizeEdge edge = do
      payload' <- normalizePayload (ePayload edge)
      pure edge { ePayload = payload' }

    normalizePayload payload =
      case payload of
        PGen g attrs bargs ->
          PGen g attrs <$> mapM normalizeBinderArg bargs
        PBox name inner ->
          PBox name <$> normalizeDiagramObjExprs mt inner
        PFeedback inner ->
          PFeedback <$> normalizeDiagramObjExprs mt inner
        PTmMeta v -> do
          sort' <- normalizeObjExpr mt (tmvSort v)
          pure (PTmMeta v { tmvSort = sort' })
        PSplice x ->
          pure (PSplice x)
        PInternalDrop ->
          pure PInternalDrop

    normalizeBinderArg barg =
      case barg of
        BAConcrete inner ->
          BAConcrete <$> normalizeDiagramObjExprs mt inner
        BAMeta v ->
          pure (BAMeta v)
