{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ModAction
  ( applyModExpr
  , mapTypeByModExpr
  , mapTypeByModExprWithLift
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
import Strat.Poly.Cell2 (Cell2(..), c2TyVars)
import Strat.Poly.Doctrine
import Strat.Poly.Graph
import Strat.Poly.Diagram
import Strat.Poly.DiagramInterpretation
  ( DiagramInterpretation(..)
  , applySubstBinderSig
  , applySubstBinderSigs
  , binderHoleCaptureRiskMetasDiagram
  , binderHoleNames
  , instantiateGenImageBindersWithMapper
  , interpretDiagram
  , renameBinderArgMetas
  , requirePortType
  , spliceEdge
  , stableHoleCaptureRenaming
  )
import Strat.Poly.ModeTheory
import Strat.Poly.Normalize (autoJoinProofWithMapper)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Proof
  ( JoinProof
  , SearchBudget
  , SearchLimit
  , SearchOutcome(..)
  , defaultSearchBudget
  , renderSearchLimit
  , checkJoinProofWithMapper
  )
import Strat.Poly.Rewrite (rulesFromPolicy)
import Strat.Poly.Obj
import Strat.Poly.UnifyObj hiding (applySubstDiagram)
import Strat.Poly.TypeTheory
import Strat.Poly.DefEq (termExprToDiagramChecked)
import Strat.Poly.TermExpr (TermExpr(..))

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
      let explicit = explicitActionGenSet srcMode action
      let srcRules =
            [ c
            | c <- dCells2 doc
            , dMode (c2LHS c) == srcMode
            , ruleUsesOnly explicit c
            ]
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
      proof <- autoJoinProofWithMapper (applyModExpr doc) tt budget rules lhs rhs
      case proof of
        SearchUndecided lim ->
          Right
            ( ActionSemanticsUndecided
                ("rule " <> c2Name cell)
                lim
            )
        SearchProved witness -> do
          checkJoinProofWithMapper (applyModExpr doc) tt rules witness
          Right (ActionSemanticsProved [("rule " <> c2Name cell, witness)])

    checkModEqn tt ctorTables eqn = do
      let lhs = meLHS eqn
      let rhs = meRHS eqn
      let mods = mePath lhs <> mePath rhs
      if all (`M.member` dActions doc) mods
        then do
          explicitCommon <- explicitIntersection mods
          let srcMode = meSrc lhs
          let gens =
                [ gd
                | gd <- M.elems (M.findWithDefault M.empty srcMode (dGens doc))
                , gdName gd `S.member` explicitCommon
                , not (isTypeDeclGenNameInTables doc ctorTables srcMode (ObjName (renderGenName (gdName gd))))
                ]
          let policy = choosePolicy mods
          let rules = rulesFromPolicy policy (dCells2 doc)
          checkGens tt lhs rhs rules gens
        else Right (ActionSemanticsProved [])
      where
        explicitIntersection modNames =
          case mapM explicitForMod modNames of
            Left err -> Left err
            Right [] -> Right S.empty
            Right (s:ss) -> Right (foldl S.intersection s ss)

        explicitForMod modName = do
          decl <-
            case M.lookup modName (mtDecls (dModes doc)) of
              Nothing -> Left "validateDoctrine: action references unknown modality"
              Just d -> Right d
          action <-
            case M.lookup modName (dActions doc) of
              Nothing -> Left "validateDoctrine: action references unknown modality"
              Just a -> Right a
          Right (explicitActionGenSet (mdSrc decl) action)

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
      proof <- autoJoinProofWithMapper (applyModExpr doc) tt budget rules lhsMapped rhsMapped
      case proof of
        SearchUndecided lim ->
          Right
            ( ActionSemanticsUndecided
                ("generator " <> renderGenName (gdName gd))
                lim
            )
        SearchProved witness -> do
          checkJoinProofWithMapper (applyModExpr doc) tt rules witness
          Right (ActionSemanticsProved [("generator " <> renderGenName (gdName gd), witness)])

    choosePolicy mods =
      let policies = [ maPolicy action | m <- mods, action <- maybeToList (M.lookup m (dActions doc)) ]
       in case policies of
            [] -> UseStructuralAsBidirectional
            (p:ps) ->
              if all (== p) ps
                then p
                else UseStructuralAsBidirectional

    explicitActionGenSet srcMode action =
      S.fromList
        [ g
        | ((srcMode', g), _) <- M.toList (maGenMap action)
        , srcMode' == srcMode
        ]

    ruleUsesOnly explicit cell =
      S.isSubsetOf (diagramGens (c2LHS cell) `S.union` diagramGens (c2RHS cell)) explicit

    diagramGens diag =
      foldMap edgeGens (IM.elems (dEdges diag))

    edgeGens edge =
      case ePayload edge of
        PGen g _ bargs ->
          S.insert g (foldMap binderArgGens bargs)
        PProvider _ ->
          S.empty
        PModuleRef _ ->
          S.empty
        PBox _ inner ->
          diagramGens inner
        PFeedback inner ->
          diagramGens inner
        PSplice _ _ ->
          S.empty
        PTmMeta _ ->
          S.empty
        PInternalDrop ->
          S.empty

    binderArgGens barg =
      case barg of
        BAConcrete inner -> diagramGens inner
        BAMeta _ -> S.empty

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
              [ (tmVarOwner v, tmvName v)
              | v <- S.toList (S.union (freeVarsDiagram (c2LHS cell)) (freeVarsDiagram (c2RHS cell)))
              ]
      let (substMap, _used) = foldl freshOne (M.empty, used0) vars
      subst <- mkSubst [ (v, CAObj t) | (v, t) <- M.toList substMap ]
      lhs <- applySubstDiagram tt subst (c2LHS cell)
      rhs <- applySubstDiagram tt subst (c2RHS cell)
      pure cell { c2LHS = lhs, c2RHS = rhs }
  where
    freshOne (acc, used) v =
      let name' = pickFresh used (tyVarMode v) ("actchk_" <> tmvName v) 0
          v' = v { tmvName = name' }
          used' = S.insert (tyVarMode v', tmvName v') used
          acc' = M.insert v (OVar v') acc
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

firstText :: (Text -> Text) -> Either Text a -> Either Text a
firstText f mv =
  case mv of
    Left err -> Left (f err)
    Right v -> Right v

renderGenName :: GenName -> Text
renderGenName (GenName g) = g

mapTypeByModExpr :: Doctrine -> ModExpr -> Obj -> Either Text Obj
mapTypeByModExpr doc me ty = do
  codeLift <- classifierLiftForModExpr (dModes doc) me
  mapTypeByModExprWithLift doc me codeLift ty

mapTypeByModExprWithLift :: Doctrine -> ModExpr -> ModExpr -> Obj -> Either Text Obj
mapTypeByModExprWithLift doc me codeLift ty =
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
          , diMapSplice = \x me0 -> do
              if meTgt me0 == mdSrc decl
                then Right ()
                else Left "map: splice modality context target mismatch"
              let composed =
                    ModExpr
                      { meSrc = meSrc me0
                      , meTgt = mdTgt decl
                      , mePath = mePath me0 <> [mName]
                      }
              let normalized = normalizeModExpr (dModes doc) composed
              if meSrc normalized == meSrc me0 && meTgt normalized == mdTgt decl
                then Right (x, normalized)
                else Left "map: splice modality context normalization changed endpoints"
          , diOnGenEdge = onGenEdge tt mName me codeLift
          }
  interpretDiagram interp diagSrc
  where
    stableCaptureRenaming =
      stableHoleCaptureRenaming
        (binderHoleCaptureRiskMetasDiagram diagSrc)
        (binderArgMetaVarsDiagram diagSrc)

    mapType me codeLift = mapTypeWithLift (dModes doc) me codeLift

    mapTypeIfSource me codeLift ty =
      if objOwnerMode ty == meSrc me
        then mapType me codeLift ty
        else pure ty

    onGenEdge tt modName me codeLift diagSrc0 diagTgt edgeKey edgeSrc mappedBargs =
      case ePayload edgeSrc of
        PGen g args _bargsSrc -> do
          genDecl0 <- lookupGenDeclInDoctrine "map: unknown source generator" doc (dMode diagSrc0) g
          img0raw <- actionImageForGenerator tt doc modName g
          (genDecl, img0base) <- freshenGenDeclAndImage tt edgeKey genDecl0 img0raw
          let protectedVars = S.fromList (gdTyVars genDecl <> gdTmVars genDecl)
          (img0, renameSubst) <- freshenImageTyVars tt protectedVars diagTgt img0base
          argSubst <- instantiateGenParams tt genDecl args
          img1 <- applySubstDiagram tt argSubst img0
          (img2, subst) <-
            firstText
              (\err -> "map: generator " <> renderGenName g <> " boundary instantiation failed: " <> err)
              (instantiateImage tt diagTgt edgeKey img1)
          img3 <-
            firstText
              (\err -> "map: generator " <> renderGenName g <> " binder instantiation failed: " <> err)
              (instantiateMappedBinders tt me codeLift genDecl mappedBargs renameSubst subst img2)
          img4 <- weakenDiagramTmCtxTo (dTmCtx diagTgt) img3
          diagTgtNorm <- normalizeBoundaryPorts (eIns edgeSrc <> eOuts edgeSrc) diagTgt
          img4Norm <- normalizeDiagramObjExprs (dModes doc) img4
          spliceEdge diagTgtNorm edgeKey img4Norm
        _ ->
          Left "map: internal error: diOnGenEdge called on non-PGen"

    freshenGenDeclAndImage
      :: TypeTheory
      -> Int
      -> GenDecl
      -> Diagram
      -> Either Text (GenDecl, Diagram)
    freshenGenDeclAndImage typeTheory edgeIdx genDecl image0 = do
      (freshParams, renameSubst) <- freshenSourceParams typeTheory edgeIdx (gdParams genDecl)
      domFresh <- mapM (renameInputShape typeTheory renameSubst) (gdDom genDecl)
      codFresh <- applySubstCtx typeTheory renameSubst (gdCod genDecl)
      imageFresh <- applySubstDiagram typeTheory renameSubst image0
      pure
        ( genDecl
            { gdParams = freshParams
            , gdDom = domFresh
            , gdCod = codFresh
            }
        , imageFresh
        )

    freshenSourceParams
      :: TypeTheory
      -> Int
      -> [GenParam]
      -> Either Text ([GenParam], Subst)
    freshenSourceParams typeTheory edgeIdx =
      go 0 emptySubst []
      where
        go _ subst acc [] =
          Right (reverse acc, subst)
        go i subst acc (param : rest) =
          case param of
            GP_Ty v -> do
              sort' <- applySubstObj typeTheory subst (tmvSort v)
              let fresh = freshTyParamVar edgeIdx i v sort'
              singleton <- mkSubst [(v, CAObj (OVar fresh))]
              subst' <- composeSubst typeTheory singleton subst
              go (i + 1) subst' (GP_Ty fresh : acc) rest
            GP_Tm v -> do
              sort' <- applySubstObj typeTheory subst (tmvSort v)
              let fresh = freshTmParamVar edgeIdx i v sort'
              tmFresh <- termExprToDiagramChecked typeTheory [] sort' (TMMeta fresh [])
              singleton <- mkSubst [(v, CATm tmFresh)]
              subst' <- composeSubst typeTheory singleton subst
              go (i + 1) subst' (GP_Tm fresh : acc) rest

    renameInputShape :: TypeTheory -> Subst -> InputShape -> Either Text InputShape
    renameInputShape typeTheory subst shape =
      case shape of
        InPort ty -> InPort <$> applySubstObj typeTheory subst ty
        InBinder sig -> InBinder <$> applySubstBinderSig typeTheory subst sig

    freshTyParamVar :: Int -> Int -> TmVar -> Obj -> TmVar
    freshTyParamVar edgeIdx i v sort' =
      v
        { tmvName = tmvName v <> "__map" <> T.pack (show edgeIdx) <> "_" <> T.pack (show i)
        , tmvSort = sort'
        }

    freshTmParamVar :: Int -> Int -> TmVar -> Obj -> TmVar
    freshTmParamVar edgeIdx i v sort' =
      v
        { tmvName = tmvName v <> "__map" <> T.pack (show edgeIdx) <> "_" <> T.pack (show i)
        , tmvSort = sort'
        , tmvOwnerMode = Nothing
        }

    instantiateMappedBinders
      :: TypeTheory
      -> ModExpr
      -> ModExpr
      -> GenDecl
      -> [BinderArg]
      -> Subst
      -> Subst
      -> Diagram
      -> Either Text Diagram
    instantiateMappedBinders typeTheory me codeLift genDecl mappedBargs renameSubst subst image = do
      let slots = [ bs | InBinder bs <- gdDom genDecl ]
      if length slots /= length mappedBargs
        then Left "map: source binder argument arity mismatch"
        else Right ()
      let holes = binderHoleNames (length slots)
      let mappedBargs' = renameBinderArgMetas stableCaptureRenaming mappedBargs
      sigs0 <- mapM mapBinderSig (M.fromList (zip holes slots))
      sigs1 <- applySubstBinderSigs typeTheory renameSubst sigs0
      sigs <- applySubstBinderSigs typeTheory subst sigs1
      let holeSub = M.fromList (zip holes mappedBargs')
      out <- instantiateGenImageBindersWithMapper typeTheory (applyModExpr doc) sigs holeSub image
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

    freshenImageTyVars
      :: TypeTheory
      -> S.Set TmVar
      -> Diagram
      -> Diagram
      -> Either Text (Diagram, Subst)
    freshenImageTyVars typeTheory protected host image = do
      let vars = S.toList (S.difference (freeVarsDiagram image) protected)
      if null vars
        then do
          subst <- mkSubst []
          pure (image, subst)
        else do
          let used0 = S.fromList [ (tmVarOwner v, tmvName v) | v <- S.toList (freeVarsDiagram host) ]
          let (_, pairsRev) = foldl freshOne (used0, []) vars
          subst <- mkSubst [ (v, CAObj t) | (v, t) <- reverse pairsRev ]
          image' <- applySubstDiagram typeTheory subst image
          pure (image', subst)
      where
        freshOne (used, acc) v =
          let name' = pickFresh used (tyVarMode v) (tmvName v <> "_img") 0
              v' = v { tmvName = name' }
              used' = S.insert (tyVarMode v', tmvName v') used
           in (used', (v, OVar v') : acc)

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
  let flex = freeVarsDiagram img
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
        PGen g args bargs ->
          PGen g args <$> mapM normalizeBinderArg bargs
        PProvider ref ->
          pure (PProvider ref)
        PModuleRef ref ->
          pure (PModuleRef ref)
        PBox name inner ->
          PBox name <$> normalizeDiagramObjExprs mt inner
        PFeedback inner ->
          PFeedback <$> normalizeDiagramObjExprs mt inner
        PTmMeta v -> do
          sort' <- normalizeObjExpr mt (tmvSort v)
          pure (PTmMeta v { tmvSort = sort' })
        PSplice x me ->
          pure (PSplice x me)
        PInternalDrop ->
          pure PInternalDrop

    normalizeBinderArg barg =
      case barg of
        BAConcrete inner ->
          BAConcrete <$> normalizeDiagramObjExprs mt inner
        BAMeta v ->
          pure (BAMeta v)
