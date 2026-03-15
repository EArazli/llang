{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DSL.Elab.Diag
  ( BinderMetaMode(..)
  , elabRuleLHS
  , elabRuleRHS
  , elabDiagExpr
  , elabDiagExprInScope
  , elabDiagExprWith
  , elabDiagExprWithInScope
  , lookupGen
  , unifyBoundary
  , mkForGenDiag
  , renderGenName
  , ensureMode
  , renderModeName
  , ensureAcyclicMode
  , topologicalEdges
  ) where

import Control.Monad (foldM)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Data.Maybe (catMaybes)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Frontend.Coerce (coerceDiagramTo)
import Strat.Frontend.Env (ModuleEnv(..), ScopedValue(..))
import Strat.Poly.DSL.AST
import Strat.Poly.DSL.Elab.Resolve (elabRawModExpr)
import Strat.Poly.DSL.Elab.Term
  ( elabContextWithTables
  , elabObjExprWithTablesInScope
  , elabTmTermInScope
  , mkTypeMetaVar
  , ownerModeForTypeMeta
  )
import Strat.Poly.DefEq (normalizeObjDeep, termExprToDiagramChecked)
import Strat.Poly.Diagram
import Strat.Poly.Doctrine
import Strat.Poly.Graph
  ( BinderArg(..)
  , BinderMetaVar(..)
  , Edge(..)
  , EdgeId(..)
  , EdgePayload(..)
  , PortId(..)
  , addEdgePayload
  , diagramPortObj
  , emptyDiagram
  , freshPort
  , setPortLabel
  , validateDiagram
  )
import Strat.Poly.ModeTheory
import Strat.Poly.ModAction (applyModExpr)
import Strat.Poly.Names
import Strat.Poly.Obj
import qualified Strat.Poly.TeleArgs as TA
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.TypeTheory (TypeTheory(..), literalKindForObj, ttCtorTablesByOwner)
import qualified Strat.Poly.UnifyObj as U

renderGenName :: GenName -> Text
renderGenName (GenName n) = n

ensureMode :: Doctrine -> ModeName -> Either Text ()
ensureMode doc mode =
  if M.member mode (mtModes (dModes doc))
    then Right ()
    else Left "unknown mode"

renderModeName :: ModeName -> Text
renderModeName (ModeName name) = name

data AlphaVarState = AlphaVarState
  { avsForward :: M.Map TmVar TmVar
  , avsBackward :: M.Map TmVar TmVar
  }

binderSigAlphaEq :: BinderSig -> BinderSig -> Bool
binderSigAlphaEq lhs rhs =
  case alphaCtx alphaEmpty (bsTmCtx lhs) (bsTmCtx rhs) of
    Nothing -> False
    Just st1 ->
      case alphaCtx st1 (bsDom lhs) (bsDom rhs) of
        Nothing -> False
        Just st2 -> maybe False (const True) (alphaCtx st2 (bsCod lhs) (bsCod rhs))
  where
    alphaEmpty = AlphaVarState M.empty M.empty

    alphaCtx st xs ys
      | length xs /= length ys = Nothing
      | otherwise = foldM (\st' (x, y) -> alphaObj st' x y) st (zip xs ys)

    alphaArg st argL argR =
      case (argL, argR) of
        (OAObj objL, OAObj objR) -> alphaObj st objL objR
        (OATm tmL, OATm tmR)
          | tmL == tmR -> Just st
          | otherwise -> Nothing
        _ -> Nothing

    alphaVar st vL vR =
      if tmVarOwner vL /= tmVarOwner vR
        then Nothing
        else
          case (M.lookup vL (avsForward st), M.lookup vR (avsBackward st)) of
            (Just mapped, Just mappedBack)
              | mapped == vR && mappedBack == vL -> Just st
              | otherwise -> Nothing
            (Nothing, Nothing) -> do
              st' <- alphaObj st (tmvSort vL) (tmvSort vR)
              Just
                st'
                  { avsForward = M.insert vL vR (avsForward st')
                  , avsBackward = M.insert vR vL (avsBackward st')
                  }
            _ -> Nothing

    alphaObj st objL objR =
      case (objL, objR) of
        (OVar vL, OVar vR) -> alphaVar st vL vR
        (OCon refL argsL, OCon refR argsR)
          | refL == refR && length argsL == length argsR ->
              foldM (\st' (x, y) -> alphaArg st' x y) st (zip argsL argsR)
          | otherwise -> Nothing
        (OLift meL innerL, OLift meR innerR)
          | meL == meR -> alphaObj st innerL innerR
          | otherwise -> Nothing
        _ -> Nothing

data BinderMetaMode
  = BMNoMeta
  | BMCollect
  | BMUse
  deriving (Eq, Show)

elabRuleLHS
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> RawDiagExpr
  -> Either Text (Diagram, M.Map BinderMetaVar BinderSig)
elabRuleLHS env doc mode tyVars tmVars expr = do
  (diag, metas) <- elabDiagExprWith env doc mode [] tyVars tmVars M.empty BMCollect False False expr
  ensureAcyclicMode doc mode diag
  pure (diag, metas)

elabRuleRHS
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [TmVar]
  -> [TmVar]
  -> M.Map BinderMetaVar BinderSig
  -> RawDiagExpr
  -> Either Text Diagram
elabRuleRHS env doc mode tyVars tmVars binderSigs expr = do
  (diag, metas) <- elabDiagExprWith env doc mode [] tyVars tmVars binderSigs BMUse True False expr
  if metas == binderSigs
    then do
      ensureAcyclicMode doc mode diag
      pure diag
    else Left "rule RHS introduces fresh binder metas"

elabDiagExpr :: ModuleEnv -> Doctrine -> ModeName -> [TmVar] -> RawDiagExpr -> Either Text Diagram
elabDiagExpr = elabDiagExprInScope M.empty M.empty

elabDiagExprInScope :: M.Map Text ScopedValue -> M.Map Text Obj -> ModuleEnv -> Doctrine -> ModeName -> [TmVar] -> RawDiagExpr -> Either Text Diagram
elabDiagExprInScope valueScope typeScope env doc mode ruleVars expr = do
  (diag, _) <- elabDiagExprWithInScope valueScope typeScope env doc mode [] ruleVars [] M.empty BMNoMeta False False expr
  ensureAcyclicMode doc mode diag
  pure diag

elabDiagExprWith
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [Obj]
  -> [TmVar]
  -> [TmVar]
  -> M.Map BinderMetaVar BinderSig
  -> BinderMetaMode
  -> Bool
  -> Bool
  -> RawDiagExpr
  -> Either Text (Diagram, M.Map BinderMetaVar BinderSig)
elabDiagExprWith = elabDiagExprWithInScope M.empty M.empty

elabDiagExprWithInScope
  :: M.Map Text ScopedValue
  -> M.Map Text Obj
  -> ModuleEnv
  -> Doctrine
  -> ModeName
  -> [Obj]
  -> [TmVar]
  -> [TmVar]
  -> M.Map BinderMetaVar BinderSig
  -> BinderMetaMode
  -> Bool
  -> Bool
  -> RawDiagExpr
  -> Either Text (Diagram, M.Map BinderMetaVar BinderSig)
elabDiagExprWithInScope valueScope typeScope env doc mode tmCtx tyVars tmVars binderSigs0 metaMode allowSplice allowImplicitGenArgs expr =
  ensureLinearMetaVars expr *> evalFresh (elabDiagExprWithFresh valueScope typeScope env doc mode tmCtx tyVars tmVars binderSigs0 metaMode allowSplice allowImplicitGenArgs expr)

elabDiagExprWithFresh
  :: M.Map Text ScopedValue
  -> M.Map Text Obj
  -> ModuleEnv
  -> Doctrine
  -> ModeName
  -> [Obj]
  -> [TmVar]
  -> [TmVar]
  -> M.Map BinderMetaVar BinderSig
  -> BinderMetaMode
  -> Bool
  -> Bool
  -> RawDiagExpr
  -> Fresh (Diagram, M.Map BinderMetaVar BinderSig)
elabDiagExprWithFresh valueScope typeScope env doc mode tmCtx tyVars tmVars binderSigs0 metaMode allowSplice allowImplicitGenArgs expr = do
  ttDoc <- liftEither (doctrineTypeTheory doc)
  let ctorTables = ttCtorTablesByOwner ttDoc
  build ttDoc ctorTables tmCtx binderSigs0 expr
  where
    rigidTy = S.fromList tyVars
    rigidTm = S.fromList tmVars

    build ttDoc ctorTables curTmCtx binderSigs e =
      case e of
        RDId ctx -> do
          ctx' <- liftEither (elabContextWithTables doc ctorTables mode tyVars tmVars M.empty ctx)
          pure (idDTm mode curTmCtx ctx', binderSigs)
        RDMetaVar name -> do
          baseTyVar <- liftEither (mkTypeMetaVar doc mode ("mv_" <> name))
          (_, ty) <- freshTyVar doc baseTyVar
          let (pid, d0) = freshPort ty (emptyDiagram mode curTmCtx)
          d1 <- liftEither (setPortLabel pid name d0)
          pure (d1 { dIn = [pid], dOut = [pid] }, binderSigs)
        RDGen name Nothing Nothing ->
          case M.lookup name valueScope of
            Just scoped ->
              useScopedValue curTmCtx binderSigs name scoped
            Nothing ->
              elaborateGenerator curTmCtx binderSigs name Nothing Nothing
        RDGen name mArgs mBinderArgs ->
          elaborateGenerator curTmCtx binderSigs name mArgs mBinderArgs
        RDSplice name ->
          if allowSplice
            then do
              let meta = BinderMetaVar name
              sig <- liftEither $
                case M.lookup meta binderSigs of
                  Nothing -> Left "splice references unknown binder meta"
                  Just bs -> Right bs
              diag <- liftEither (mkSpliceDiag curTmCtx meta (bsDom sig) (bsCod sig))
              pure (diag, binderSigs)
            else liftEither (Left "splice is only allowed in RHS-like templates (rule RHS, morphism images, action images)")
        RDBox name innerExpr -> do
          (inner, binderSigs') <- build ttDoc ctorTables curTmCtx binderSigs innerExpr
          dom <- liftEither (diagramDom inner)
          cod <- liftEither (diagramCod inner)
          let (ins, diag0) = allocPorts dom (emptyDiagram mode curTmCtx)
          let (outs, diag1) = allocPorts cod diag0
          diag2 <- liftEither (addEdgePayload (PBox (BoxName name) inner) ins outs diag1)
          let diag3 = diag2 { dIn = ins, dOut = outs }
          liftEither (validateDiagram diag3)
          pure (diag3, binderSigs')
        RDTrace k bodyExpr -> do
          (inner, binderSigs') <- build ttDoc ctorTables curTmCtx binderSigs bodyExpr
          let dom = dIn inner
          let cod = dOut inner
          let inLen = length dom
          let outLen = length cod
          if k > 0
            then pure ()
            else liftEither (Left "trace: expected k > 0")
          if inLen >= k
            then pure ()
            else liftEither (Left "trace: body has fewer inputs than k")
          if outLen >= k
            then pure ()
            else liftEither (Left "trace: body has fewer outputs than k")
          let m = inLen - k
          let n = outLen - k
          let fbIns = drop m dom
          let fbOuts = drop n cod
          fbInTys <- mapM (liftEither . lookupPortTy inner) fbIns
          fbOutTys <- mapM (liftEither . lookupPortTy inner) fbOuts
          if fbInTys == fbOutTys
            then pure ()
            else liftEither (Left "trace: feedback input/output objects must match (suffix convention)")
          outerInTys <- mapM (liftEither . lookupPortTy inner) (take m dom)
          outerOutTys <- mapM (liftEither . lookupPortTy inner) (take n cod)
          let (outerIns, outer1) = allocPorts outerInTys (emptyDiagram mode curTmCtx)
          let outer2 = outer1 { dIn = outerIns }
          let (outerOuts, outer3) = allocPorts outerOutTys outer2
          let outer4 = outer3 { dOut = outerOuts }
          outer5 <- liftEither (addEdgePayload (PFeedback inner) outerIns outerOuts outer4)
          liftEither (validateDiagram outer5)
          pure (outer5, binderSigs')
        RDLoop innerExpr -> do
          (inner, binderSigs') <- build ttDoc ctorTables curTmCtx binderSigs innerExpr
          let dom = dIn inner
          let cod = dOut inner
          let k = length dom
          if k > 0
            then pure ()
            else liftEither (Left "loop: expected body to have at least one input")
          if length cod >= k
            then pure ()
            else liftEither (Left "loop: expected body to have at least as many outputs as inputs")
          let n = length cod - k
          let outerOutPortsInner = take n cod
          let fbOutPorts = drop n cod
          inTys <- mapM (liftEither . lookupPortTy inner) dom
          fbOutTys <- mapM (liftEither . lookupPortTy inner) fbOutPorts
          if inTys == fbOutTys
            then pure ()
            else liftEither (Left "loop: expected last k outputs to match inputs (suffix convention)")
          outerOutTys <- mapM (liftEither . lookupPortTy inner) outerOutPortsInner
          let (outerOuts, outer0) = allocPorts outerOutTys (emptyDiagram mode curTmCtx)
          let outer1 = outer0 { dOut = outerOuts }
          outer2 <- liftEither (addEdgePayload (PFeedback inner) [] outerOuts outer1)
          liftEither (validateDiagram outer2)
          pure (outer2, binderSigs')
        RDMap rawMe innerExpr -> do
          me <- liftEither (elabRawModExpr (dModes doc) rawMe)
          (inner, binderSigs') <-
            elabDiagExprWithFresh
              valueScope
              typeScope
              env
              doc
              (meSrc me)
              curTmCtx
              tyVars
              tmVars
              binderSigs
              metaMode
              allowSplice
              allowImplicitGenArgs
              innerExpr
          mapped <- liftEither (applyModExpr doc me inner)
          if dMode mapped == mode
            then pure (mapped, binderSigs')
            else liftEither (Left "map: mapped diagram mode does not match surrounding expression mode")
        RDComp a b -> do
          (d1, binderSigs1) <- build ttDoc ctorTables curTmCtx binderSigs a
          (d2, binderSigs2) <- build ttDoc ctorTables curTmCtx binderSigs1 b
          dComp <- liftEither (compD ttDoc d2 d1)
          pure (dComp, binderSigs2)
        RDTensor a b -> do
          (d1, binderSigs1) <- build ttDoc ctorTables curTmCtx binderSigs a
          (d2, binderSigs2) <- build ttDoc ctorTables curTmCtx binderSigs1 b
          dTen <- liftEither (tensorD d1 d2)
          pure (dTen, binderSigs2)
      where
        elaborateGenerator curTmCtx' binderSigs name mArgs mBinderArgs = do
          gen <- liftEither (lookupGen doc mode (GenName name))
          (freshParams, renameSubst) <- liftEither (TA.freshTeleParams ttDoc curTmCtx' (gdParams gen))
          let genFresh = gen { gdParams = freshParams }
          dom0 <- applySubstCtxDoc ttDoc renameSubst (gdPlainDom gen)
          cod0 <- applySubstCtxDoc ttDoc renameSubst (gdCod gen)
          binderSlots0 <- mapM (applySubstBinderSig ttDoc renameSubst) [ bs | InBinder bs <- gdDom gen ]
          (genArgs, argSubst, dom, cod, binderSlots) <-
            case mArgs of
              Nothing
                | allowImplicitGenArgs -> do
                    genArgs <- liftEither (implicitGenArgs ttDoc curTmCtx' freshParams)
                    argSubst <- liftEither (instantiateGenParams ttDoc genFresh genArgs)
                    dom <- applySubstCtxDoc ttDoc argSubst dom0
                    cod <- applySubstCtxDoc ttDoc argSubst cod0
                    binderSlots <- mapM (applySubstBinderSig ttDoc argSubst) binderSlots0
                    pure (genArgs, argSubst, dom, cod, binderSlots)
              _ -> do
                rawArgs <- liftEither (resolveGenArgs (gdParams gen) mArgs)
                args <- liftEither (normalizeGenArgs (gdParams gen) rawArgs)
                (genArgs, argSubst) <-
                  liftEither
                    ( TA.elabTeleArgsSequentialWith
                        ttDoc
                        (elabTyArg ctorTables)
                        (\expectedSort _ rawArg -> elabTmArg ttDoc curTmCtx' expectedSort rawArg)
                        freshParams
                        args
                    )
                dom <- applySubstCtxDoc ttDoc argSubst dom0
                cod <- applySubstCtxDoc ttDoc argSubst cod0
                binderSlots <- mapM (applySubstBinderSig ttDoc argSubst) binderSlots0
                pure (genArgs, argSubst, dom, cod, binderSlots)
          (binderArgs, binderSigs') <- elaborateBinderArgs ttDoc binderSigs binderSlots mBinderArgs
          diag <- liftEither (mkGenDiag curTmCtx' (gdName gen) genArgs binderArgs dom cod)
          pure (diag, binderSigs')

        useScopedValue curTmCtx' binderSigs name scoped =
          if svDoctrine scoped == dName doc
            then
              if svMode scoped /= mode
                then liftEither (Left ("value " <> name <> " has mode " <> renderModeName (svMode scoped) <> ", expected " <> renderModeName mode))
                else
                  if dTmCtx (svDiagram scoped) == curTmCtx'
                    then pure (svDiagram scoped, binderSigs)
                    else liftEither (Left ("value " <> name <> " has incompatible term context"))
            else do
              srcDoc <- liftEither (lookupDoctrine env (svDoctrine scoped))
              (doc', diag') <- liftEither (coerceDiagramTo env srcDoc (svDiagram scoped) (dName doc))
              if dName doc' /= dName doc
                then liftEither (Left ("value " <> name <> " has doctrine " <> svDoctrine scoped <> ", expected " <> dName doc))
                else if dMode diag' /= mode
                  then liftEither (Left ("value " <> name <> " has mode " <> renderModeName (dMode diag') <> ", expected " <> renderModeName mode))
                  else
                    if dTmCtx diag' == curTmCtx'
                      then pure (diag', binderSigs)
                      else liftEither (Left ("value " <> name <> " has incompatible term context"))

    elaborateBinderArgs ttDoc binderSigs binderSlots mBinderArgs =
      case (binderSlots, mBinderArgs) of
        ([], Nothing) -> pure ([], binderSigs)
        ([], Just []) -> pure ([], binderSigs)
        ([], Just _) -> liftEither (Left "generator does not accept binder arguments")
        (_:_, Nothing) -> liftEither (Left "missing generator binder arguments")
        (_, Just rawArgs) ->
          if length binderSlots /= length rawArgs
            then liftEither (Left "generator binder argument mismatch")
            else foldM step ([], binderSigs) (zip binderSlots rawArgs)
      where
        step (acc, bsMap) (slot, rawArg) =
          case rawArg of
            RBAExpr exprArg -> do
              (diagArg, _) <-
                elabDiagExprWithFresh
                  valueScope
                  typeScope
                  env
                  doc
                  mode
                  (bsTmCtx slot)
                  tyVars
                  tmVars
                  M.empty
                  BMNoMeta
                  False
                  allowImplicitGenArgs
                  exprArg
              diagArg' <- liftEither (unifyBoundary ttDoc rigidTy rigidTm (bsDom slot) (bsCod slot) diagArg)
              domArg <- liftEither (diagramDom diagArg')
              codArg <- liftEither (diagramCod diagArg')
              domArg' <- canonicalCtx ttDoc domArg
              codArg' <- canonicalCtx ttDoc codArg
              slotDom' <- canonicalCtx ttDoc (bsDom slot)
              slotCod' <- canonicalCtx ttDoc (bsCod slot)
              if domArg' == slotDom' && codArg' == slotCod'
                then pure (acc <> [BAConcrete diagArg'], bsMap)
                else liftEither (Left "binder argument boundary mismatch")
            RBAMeta name ->
              case metaMode of
                BMNoMeta ->
                  liftEither (Left "binder metavariables are only allowed in rule diagrams and generator-image templates (morphisms/actions)")
                BMCollect -> do
                  let key = BinderMetaVar name
                  case M.lookup key bsMap of
                    Nothing -> pure (acc <> [BAMeta key], M.insert key slot bsMap)
                    Just slot'
                      | binderSigAlphaEq slot' slot -> pure (acc <> [BAMeta key], bsMap)
                      | otherwise -> liftEither (Left "binder meta reused with inconsistent signature")
                BMUse -> do
                  let key = BinderMetaVar name
                  case M.lookup key bsMap of
                    Nothing -> liftEither (Left "RHS introduces unknown binder meta")
                    Just slot'
                      | binderSigAlphaEq slot' slot -> pure (acc <> [BAMeta key], bsMap)
                      | otherwise -> liftEither (Left "binder meta used with inconsistent signature")

    elabTyArg ctorTables v rawArg = do
      ownerMode <- ownerModeForTypeMeta doc v
      tyArg <- elabObjExprWithTablesInScope typeScope doc ctorTables tyVars tmVars M.empty ownerMode rawArg
      if objOwnerMode tyArg == ownerMode
        then pure tyArg
        else Left "generator type argument mode mismatch"

    elabTmArg ttDoc curTmCtx expectedSort rawArg =
      case elabTmTermInScope typeScope doc tyVars tmVars M.empty (Just expectedSort) rawArg of
        Right tm -> pure tm
        Left err ->
          case rawArg of
            RPTVar name ->
              case implicitBoundCandidate curTmCtx expectedSort of
                Right (Just idx) ->
                  case termExprToDiagramChecked ttDoc curTmCtx expectedSort (TMBound idx) of
                    Right tm -> pure tm
                    Left msg -> Left ("explicit term argument `" <> name <> "`: " <> msg)
                Right Nothing ->
                  case literalKindForObj ttDoc expectedSort of
                    Just _ -> mkImplicitLiteralMeta ttDoc curTmCtx name expectedSort
                    Nothing -> Left err
                Left msg -> Left ("explicit term argument `" <> name <> "`: " <> msg)
            _ ->
              Left err
      where
        mkImplicitLiteralMeta ttDoc' ctx name expectedSort =
          case literalKindForObj ttDoc' expectedSort of
            Just _ ->
              let fresh =
                    TmVar
                      { tmvName = name
                      , tmvSort = expectedSort
                      , tmvScope = max 0 (length (modeCtxGlobals ctx (objMode expectedSort)))
                      , tmvOwnerMode = Nothing
                      }
               in termExprToDiagramChecked ttDoc' ctx expectedSort (TMMeta fresh (defaultMetaArgs ctx fresh))
            Nothing ->
              Left "expected sort does not admit literals"

        implicitBoundCandidate ctx expectedSort = do
          expectedNorm <- normalizeObjDeep ttDoc expectedSort
          let candidates =
                [ (idx, sortTy)
                | (idx, sortTy) <- zip [0 :: Int ..] ctx
                , objOwnerMode sortTy == objOwnerMode expectedNorm
                ]
          matching <- fmap catMaybes $ mapM (matches expectedNorm) candidates
          case matching of
            [] -> Right Nothing
            [idx] -> Right (Just idx)
            _ -> Left "ambiguous bound term variable (multiple binder variables share this sort)"

        matches expectedNorm (idx, sortTy) = do
          sortNorm <- normalizeObjDeep ttDoc sortTy
          pure (if sortNorm == expectedNorm then Just idx else Nothing)

    mkGenDiag curTmCtx g args bargs dom cod = do
      let (ins, d0) = allocPorts dom (emptyDiagram mode curTmCtx)
      let (outs, d1) = allocPorts cod d0
      d2 <- addEdgePayload (PGen g args bargs) ins outs d1
      let d3 = d2 { dIn = ins, dOut = outs }
      validateDiagram d3
      pure d3

    mkSpliceDiag curTmCtx meta dom cod = do
      let (ins, d0) = allocPorts dom (emptyDiagram mode curTmCtx)
      let (outs, d1) = allocPorts cod d0
      let meId = ModExpr { meSrc = mode, meTgt = mode, mePath = [] }
      d2 <- addEdgePayload (PSplice meta meId) ins outs d1
      let d3 = d2 { dIn = ins, dOut = outs }
      validateDiagram d3
      pure d3

    lookupPortTy d pid =
      case diagramPortObj d pid of
        Nothing -> Left "diagram: internal missing port type"
        Just ty -> Right ty

    canonicalCtx ttDoc ctx = liftEither (mapM (U.applySubstObj ttDoc U.emptySubst) ctx)

    applySubstCtxDoc ttDoc subst ctx = liftEither (U.applySubstCtx ttDoc subst ctx)

    applySubstBinderSig ttDoc subst bs = do
      tmCtx' <- applySubstCtxDoc ttDoc subst (bsTmCtx bs)
      dom' <- applySubstCtxDoc ttDoc subst (bsDom bs)
      cod' <- applySubstCtxDoc ttDoc subst (bsCod bs)
      pure bs { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }

    allocPorts [] diag = ([], diag)
    allocPorts (ty:rest) diag =
      let (pid, diag1) = freshPort ty diag
          (pids, diag2) = allocPorts rest diag1
      in (pid:pids, diag2)

    lookupDoctrine env' name =
      case M.lookup name (meDoctrines env') of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just doc' -> Right doc'

metaVarsIn :: RawDiagExpr -> [Text]
metaVarsIn expr =
  case expr of
    RDId _ -> []
    RDMetaVar name -> [name]
    RDGen _ _ mBinderArgs ->
      case mBinderArgs of
        Nothing -> []
        Just args -> concatMap binderArgMetaVars args
    RDSplice _ -> []
    RDBox _ inner -> metaVarsIn inner
    RDTrace _ inner -> metaVarsIn inner
    RDLoop inner -> metaVarsIn inner
    RDMap _ inner -> metaVarsIn inner
    RDComp a b -> metaVarsIn a <> metaVarsIn b
    RDTensor a b -> metaVarsIn a <> metaVarsIn b
  where
    binderArgMetaVars barg =
      case barg of
        RBAExpr d -> metaVarsIn d
        RBAMeta _ -> []

ensureLinearMetaVars :: RawDiagExpr -> Either Text ()
ensureLinearMetaVars expr =
  case firstDup (metaVarsIn expr) of
    Nothing -> Right ()
    Just name ->
      Left
        ( "diagram metavariable `?"
            <> name
            <> "` used more than once in the same diagram; this language is linear at the diagram level. Use explicit duplication (e.g. `dup`) in a cartesian/affine mode if you intend sharing."
        )
  where
    firstDup = go S.empty
    go _ [] = Nothing
    go seen (x:xs)
      | x `S.member` seen = Just x
      | otherwise = go (S.insert x seen) xs

lookupGen :: Doctrine -> ModeName -> GenName -> Either Text GenDecl
lookupGen doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left ("unknown generator: " <> renderGen name <> " @" <> renderMode mode)
    Just gd -> Right gd
  where
    renderMode (ModeName m) = m
    renderGen (GenName g) = g

unifyBoundary :: TypeTheory -> S.Set TmVar -> S.Set TmVar -> Context -> Context -> Diagram -> Either Text Diagram
unifyBoundary tt rigidTy rigidTm dom cod diag = do
  domDiag <- diagramDom diag
  let rigid = S.union rigidTy rigidTm
  let flex0 = S.difference (freeVarsDiagram diag) rigid
  s1 <- U.unifyCtx tt (dTmCtx diag) flex0 domDiag dom
  diag1 <- applySubstDiagram tt s1 diag
  codDiag <- diagramCod diag1
  let flex1 = S.difference (freeVarsDiagram diag1) rigid
  s2 <- U.unifyCtx tt (dTmCtx diag1) flex1 codDiag cod
  applySubstDiagram tt s2 diag1

mkForGenDiag :: ModeName -> GenDecl -> Either Text Diagram
mkForGenDiag mode gen = do
  let dom = gdPlainDom gen
  let cod = gdCod gen
  args <- forGenArgs (gdParams gen)
  let bargs = forGenBinderArgs (gdDom gen)
  let (ins, d0) = allocPorts dom (emptyDiagram mode [])
  let (outs, d1) = allocPorts cod d0
  d2 <- addEdgePayload (PGen (gdName gen) args bargs) ins outs d1
  let d3 = d2 { dIn = ins, dOut = outs }
  validateDiagram d3
  pure d3
  where
    forGenArgs params =
      mapM paramArg params

    paramArg param =
      case param of
        GP_Ty v -> Right (CAObj (OVar v))
        GP_Tm v -> CATm <$> tmVarDiagram v

    tmVarDiagram v = do
      let (outPid, d0) = freshPort (tmvSort v) (emptyDiagram (objOwnerMode (tmvSort v)) [])
      d1 <- addEdgePayload (PTmMeta v) [] [outPid] d0
      let d2 = d1 { dOut = [outPid] }
      validateDiagram d2
      pure (TermDiagram d2)

    forGenBinderArgs domShapes =
      [ BAMeta (BinderMetaVar ("for_gen_b" <> T.pack (show i)))
      | (i, _) <- zip [0 :: Int ..] [ () | InBinder _ <- domShapes ]
      ]

    allocPorts [] diag = ([], diag)
    allocPorts (ty:rest) diag =
      let (pid, diag1) = freshPort ty diag
          (pids, diag2) = allocPorts rest diag1
       in (pid : pids, diag2)

ensureDistinct :: Ord a => Text -> [a] -> Either Text ()
ensureDistinct label names =
  let set = S.fromList names
   in if S.size set == length names then Right () else Left label

resolveGenArgs :: [GenParam] -> Maybe [RawGenArg] -> Either Text [RawGenArg]
resolveGenArgs params mArgs =
  case mArgs of
    Nothing
      | null params -> Right []
      | otherwise -> Left "missing generator arguments"
    Just args -> Right args

implicitGenArgs :: TypeTheory -> [Obj] -> [GenParam] -> Either Text [CodeArg]
implicitGenArgs ttDoc tmCtx params =
  mapM mkArg params
  where
    mkArg param =
      case param of
        GP_Ty v -> Right (CAObj (OVar v))
        GP_Tm v ->
          CATm <$> termExprToDiagramChecked ttDoc tmCtx (tmvSort v) (TMMeta v (defaultMetaArgs tmCtx v))

normalizeGenArgs :: [GenParam] -> [RawGenArg] -> Either Text [RawPolyObjExpr]
normalizeGenArgs params args =
  case (namedArgs, positionalArgs) of
    (_:_, _:_) -> Left "generator arguments must be either all named or all positional"
    (_:_, []) -> normalizeNamed namedArgs
    ([], _) -> normalizePos positionalArgs
  where
    namedArgs = [ (name, arg) | RGNamed name arg <- args ]
    positionalArgs = [ arg | RGPos arg <- args ]
    paramNames = map paramName params

    normalizeNamed named = do
      ensureDistinct "duplicate generator argument" (map fst named)
      if length named /= length params
        then Left "generator argument mismatch"
        else Right ()
      if S.fromList (map fst named) == S.fromList paramNames
        then Right ()
        else Left "generator arguments must cover exactly the declared parameters"
      let namedMap = M.fromList named
      mapM
        (\param ->
          case M.lookup (paramName param) namedMap of
            Nothing -> Left "missing generator argument"
            Just arg -> Right arg
        )
        params

    normalizePos positional =
      if length positional /= length params
        then Left "generator argument mismatch"
        else Right positional

    paramName param =
      case param of
        GP_Ty v -> tmvName v
        GP_Tm v -> tmvName v

ensureAcyclicMode :: Doctrine -> ModeName -> Diagram -> Either Text ()
ensureAcyclicMode doc mode diag =
  if modeIsAcyclic doc mode
    then do
      _ <- topologicalEdges diag
      mapM_ checkInner (IM.elems (dEdges diag))
    else Right ()
  where
    checkInner edge =
      case ePayload edge of
        PBox _ inner -> ensureAcyclicMode doc mode inner
        PFeedback inner -> ensureAcyclicMode doc mode inner
        _ -> Right ()

topologicalEdges :: Diagram -> Either Text [Edge]
topologicalEdges diag =
  if IM.null edgeTable
    then Right []
    else
      if length orderedIds == IM.size edgeTable
        then mapM lookupEdge orderedIds
        else Left "acyclic mode violation: diagram contains a cycle"
  where
    edgeTable = dEdges diag
    edgeIds = map eId (IM.elems edgeTable)

    deps0 = M.fromList [(eid, depsFor eid) | eid <- edgeIds]
    dependents = foldl insertDeps M.empty (M.toList deps0)

    insertDeps acc (eid, deps) =
      S.foldl' (\m dep -> M.insertWith S.union dep (S.singleton eid) m) acc deps

    depsFor eid =
      case findEdge eid of
        Nothing -> S.empty
        Just edge ->
          S.fromList
            [ prod
            | p <- eIns edge
            , Just (Just prod) <- [IM.lookup (portInt p) (dProd diag)]
            ]

    ready0 =
      S.fromList
        [ eid
        | (eid, deps) <- M.toList deps0
        , S.null deps
        ]

    orderedIds = go ready0 deps0 []

    go ready deps acc =
      case S.lookupMin ready of
        Nothing -> reverse acc
        Just eid ->
          let readyRest = S.deleteMin ready
              out = M.findWithDefault S.empty eid dependents
              (deps', ready') = S.foldl' (dropDep eid) (deps, readyRest) out
           in go ready' deps' (eid : acc)

    dropDep done (deps, ready) target =
      let old = M.findWithDefault S.empty target deps
          new = S.delete done old
          deps' = M.insert target new deps
          ready' = if S.null new then S.insert target ready else ready
       in (deps', ready')

    findEdge eid =
      let EdgeId k = eid
       in IM.lookup k edgeTable

    lookupEdge eid =
      case findEdge eid of
        Nothing -> Left "internal error: missing edge"
        Just edge -> Right edge

    portInt (PortId i) = i

-- Freshening monad

newtype Fresh a = Fresh (Int -> Either Text (a, Int))

instance Functor Fresh where
  fmap f (Fresh g) =
    Fresh (\n -> do
      (a, n') <- g n
      pure (f a, n'))

instance Applicative Fresh where
  pure a = Fresh (\n -> Right (a, n))
  Fresh f <*> Fresh g =
    Fresh (\n -> do
      (h, n1) <- f n
      (a, n2) <- g n1
      pure (h a, n2))

instance Monad Fresh where
  Fresh g >>= k =
    Fresh (\n -> do
      (a, n1) <- g n
      let Fresh h = k a
      h n1)

evalFresh :: Fresh a -> Either Text a
evalFresh (Fresh f) = fmap fst (f 0)

freshTyVar :: Doctrine -> TmVar -> Fresh (TmVar, Obj)
freshTyVar doc v = do
  n <- freshInt
  let name = tmvName v <> T.pack ("#" <> show n)
  let fresh = v { tmvName = name }
  ownerMode <- liftEither (ownerModeForTypeMeta doc v)
  pure (v, Obj { objOwnerMode = ownerMode, objCode = CTMeta fresh })

freshInt :: Fresh Int
freshInt = Fresh (\n -> Right (n, n + 1))

liftEither :: Either Text a -> Fresh a
liftEither (Left err) = Fresh (\_ -> Left err)
liftEither (Right a) = pure a
