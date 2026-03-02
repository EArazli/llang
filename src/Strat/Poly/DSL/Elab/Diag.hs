{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.DSL.Elab.Diag
  ( BinderMetaMode(..)
  , elabRuleLHS
  , elabRuleRHS
  , elabDiagExpr
  , elabDiagExprWith
  , lookupGen
  , unifyBoundary
  , mkForGenDiag
  , renderGenName
  , ensureMode
  , renderModeName
  , ensureAttrSort
  , ensureAcyclicMode
  ) where

import Control.Monad (foldM)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Data.Maybe (catMaybes)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Frontend.Coerce (coerceDiagramTo)
import Strat.Frontend.Env (ModuleEnv(..), TermDef(..))
import Strat.Poly.Attr
import Strat.Poly.DSL.AST
import Strat.Poly.DSL.Elab.Resolve (elabRawModExpr)
import Strat.Poly.DSL.Elab.Term
  ( elabContextWithTables
  , elabObjExprWithTables
  , elabTmTerm
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
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.TypeTheory (TypeTheory(..), ttCtorTablesByOwner)
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

ensureAttrSort :: Doctrine -> AttrSort -> Either Text ()
ensureAttrSort doc sortName =
  if M.member sortName (dAttrSorts doc)
    then Right ()
    else Left "unknown attribute sort"

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
  (diag, metas) <- elabDiagExprWith env doc mode [] tyVars tmVars M.empty BMCollect False expr
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram diag)
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
  (diag, metas) <- elabDiagExprWith env doc mode [] tyVars tmVars binderSigs BMUse True expr
  if metas == binderSigs
    then do
      ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram diag)
      ensureAcyclicMode doc mode diag
      pure diag
    else Left "rule RHS introduces fresh binder metas"

elabDiagExpr :: ModuleEnv -> Doctrine -> ModeName -> [TmVar] -> RawDiagExpr -> Either Text Diagram
elabDiagExpr env doc mode ruleVars expr = do
  (diag, _) <- elabDiagExprWith env doc mode [] ruleVars [] M.empty BMNoMeta False expr
  ensureAttrVarNameSortsDiagram (freeAttrVarsDiagram diag)
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
  -> RawDiagExpr
  -> Either Text (Diagram, M.Map BinderMetaVar BinderSig)
elabDiagExprWith env doc mode tmCtx tyVars tmVars binderSigs0 metaMode allowSplice expr =
  ensureLinearMetaVars expr *> evalFresh (elabDiagExprWithFresh env doc mode tmCtx tyVars tmVars binderSigs0 metaMode allowSplice expr)

elabDiagExprWithFresh
  :: ModuleEnv
  -> Doctrine
  -> ModeName
  -> [Obj]
  -> [TmVar]
  -> [TmVar]
  -> M.Map BinderMetaVar BinderSig
  -> BinderMetaMode
  -> Bool
  -> RawDiagExpr
  -> Fresh (Diagram, M.Map BinderMetaVar BinderSig)
elabDiagExprWithFresh env doc mode tmCtx tyVars tmVars binderSigs0 metaMode allowSplice expr = do
  ttDoc <- liftEither (doctrineTypeTheory doc)
  let ctorTables = ttCtorTablesByOwner ttDoc
  build ttDoc ctorTables tmCtx binderSigs0 expr
  where
    rigidTy = S.fromList tyVars
    rigidTm = S.fromList tmVars

    elabOneParamArg ttDoc ctorTables curTmCtx tyFreshMap tmFreshMap (tyAcc, tmAcc) (paramKind, rawArg) =
      case paramKind of
        GP_Ty tyVar0 -> do
          freshTyParam <-
            case M.lookup tyVar0 tyFreshMap of
              Nothing -> liftEither (Left "internal error: missing fresh type parameter")
              Just v -> pure v
          ownerMode <- liftEither (ownerModeForTypeMeta doc freshTyParam)
          tyArg <- liftEither (elabObjExprWithTables doc ctorTables tyVars tmVars M.empty ownerMode rawArg)
          if objOwnerMode tyArg == ownerMode
            then pure ((freshTyParam, tyArg) : tyAcc, tmAcc)
            else liftEither (Left "generator type argument mode mismatch")
        GP_Tm tmVar0 -> do
          freshTmParam <-
            case M.lookup tmVar0 tmFreshMap of
              Nothing -> liftEither (Left "internal error: missing fresh term parameter")
              Just v -> pure v
          tmArg <- elabTmArg ttDoc curTmCtx freshTmParam rawArg
          pure (tyAcc, (freshTmParam, tmArg) : tmAcc)

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
        RDGen name mArgs mAttrArgs mBinderArgs -> do
          gen <- liftEither (lookupGen doc mode (GenName name))
          tyRename <- freshTySubst doc (gdTyVars gen)
          tmRename <- freshTmSubst ttDoc curTmCtx (gdTmVars gen)
          renameSubst <-
            liftEither
              ( U.mkSubst
                  ( [ (v, CAObj ty)
                    | (v, ty) <- M.toList tyRename
                    ]
                      <> [ (v, CATm tm)
                         | (v, tm) <- M.toList tmRename
                         ]
                  )
              )
          dom0 <- applySubstCtxDoc ttDoc renameSubst (gdPlainDom gen)
          cod0 <- applySubstCtxDoc ttDoc renameSubst (gdCod gen)
          binderSlots0 <- mapM (applySubstBinderSig ttDoc renameSubst) [ bs | InBinder bs <- gdDom gen ]
          (dom, cod, binderSlots) <-
            case mArgs of
              Nothing -> pure (dom0, cod0, binderSlots0)
              Just args -> do
                let paramOrder = gdParams gen
                if length args /= length paramOrder
                  then liftEither (Left "generator type/term argument mismatch")
                  else do
                    freshTyVars <- liftEither (extractFreshTyVars (gdTyVars gen) tyRename)
                    freshTmVars <- liftEither (extractFreshTmVars (gdTmVars gen) tmRename)
                    let tyFreshMap = M.fromList (zip (gdTyVars gen) freshTyVars)
                    let tmFreshMap = M.fromList (zip (gdTmVars gen) freshTmVars)
                    (tyBinds, tmBinds) <-
                      foldM
                        (elabOneParamArg ttDoc ctorTables curTmCtx tyFreshMap tmFreshMap)
                        ([], [])
                        (zip paramOrder args)
                    argSubst <-
                      liftEither
                        ( U.mkSubst
                            ( [ (v, CAObj ty)
                              | (v, ty) <- reverse tyBinds
                              ]
                                <> [ (v, CATm tm)
                                   | (v, tm) <- reverse tmBinds
                                   ]
                            )
                        )
                    dom1 <- applySubstCtxDoc ttDoc argSubst dom0
                    cod1 <- applySubstCtxDoc ttDoc argSubst cod0
                    binderSlots1 <- mapM (applySubstBinderSig ttDoc argSubst) binderSlots0
                    pure (dom1, cod1, binderSlots1)
          attrs <- liftEither (elabGenAttrs doc gen mAttrArgs)
          (binderArgs, binderSigs') <- elaborateBinderArgs ttDoc binderSigs binderSlots mBinderArgs
          diag <- liftEither (mkGenDiag curTmCtx (gdName gen) attrs binderArgs dom cod)
          pure (diag, binderSigs')
        RDTermRef name -> do
          term <- liftEither (lookupTerm env name)
          if tdDoctrine term == dName doc
            then
              if tdMode term /= mode
                then liftEither (Left ("term @" <> name <> " has mode " <> renderModeName (tdMode term) <> ", expected " <> renderModeName mode))
                else
                  if dTmCtx (tdDiagram term) == curTmCtx
                    then pure (tdDiagram term, binderSigs)
                    else liftEither (Left ("term @" <> name <> " has incompatible term context"))
            else do
              srcDoc <- liftEither (lookupDoctrine env (tdDoctrine term))
              (doc', diag') <- liftEither (coerceDiagramTo env srcDoc (tdDiagram term) (dName doc))
              if dName doc' /= dName doc
                then liftEither (Left ("term @" <> name <> " has doctrine " <> tdDoctrine term <> ", expected " <> dName doc))
                else if dMode diag' /= mode
                  then liftEither (Left ("term @" <> name <> " has mode " <> renderModeName (dMode diag') <> ", expected " <> renderModeName mode))
                  else
                    if dTmCtx diag' == curTmCtx
                      then pure (diag', binderSigs)
                      else liftEither (Left ("term @" <> name <> " has incompatible term context"))
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
            else liftEither (Left "splice is only allowed in rule RHS")
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
              env
              doc
              (meSrc me)
              curTmCtx
              tyVars
              tmVars
              binderSigs
              metaMode
              allowSplice
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
                  env
                  doc
                  mode
                  (bsTmCtx slot)
                  tyVars
                  tmVars
                  M.empty
                  BMNoMeta
                  False
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
                  liftEither (Left "binder metavariables are only allowed in rule diagrams")
                BMCollect -> do
                  let key = BinderMetaVar name
                  case M.lookup key bsMap of
                    Nothing -> pure (acc <> [BAMeta key], M.insert key slot bsMap)
                    Just slot'
                      | slot' == slot -> pure (acc <> [BAMeta key], bsMap)
                      | otherwise -> liftEither (Left "binder meta reused with inconsistent signature")
                BMUse -> do
                  let key = BinderMetaVar name
                  case M.lookup key bsMap of
                    Nothing -> liftEither (Left "RHS introduces unknown binder meta")
                    Just slot'
                      | slot' == slot -> pure (acc <> [BAMeta key], bsMap)
                      | otherwise -> liftEither (Left "binder meta used with inconsistent signature")

    elabTmArg ttDoc curTmCtx v rawArg =
      case elabTmTerm doc tyVars tmVars M.empty (Just (tmvSort v)) rawArg of
        Right tm -> pure tm
        Left err ->
          case rawArg of
            RPTVar name ->
              case implicitBoundCandidate curTmCtx (tmvSort v) of
                Right (Just idx) ->
                  case termExprToDiagramChecked ttDoc curTmCtx (tmvSort v) (TMBound idx) of
                    Right tm -> pure tm
                    Left msg -> liftEither (Left ("explicit term argument `" <> name <> "`: " <> msg))
                Right Nothing -> liftEither (Left err)
                Left msg -> liftEither (Left ("explicit term argument `" <> name <> "`: " <> msg))
            _ ->
              liftEither (Left err)
      where
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

    mkGenDiag curTmCtx g attrs bargs dom cod = do
      let (ins, d0) = allocPorts dom (emptyDiagram mode curTmCtx)
      let (outs, d1) = allocPorts cod d0
      d2 <- addEdgePayload (PGen g attrs bargs) ins outs d1
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

    lookupTerm env' name =
      case M.lookup name (meTerms env') of
        Nothing -> Left ("unknown term: " <> name)
        Just term -> Right term

    lookupDoctrine env' name =
      case M.lookup name (meDoctrines env') of
        Nothing -> Left ("Unknown doctrine: " <> name)
        Just doc' -> Right doc'

metaVarsIn :: RawDiagExpr -> [Text]
metaVarsIn expr =
  case expr of
    RDId _ -> []
    RDMetaVar name -> [name]
    RDGen _ _ _ mBinderArgs ->
      case mBinderArgs of
        Nothing -> []
        Just args -> concatMap binderArgMetaVars args
    RDTermRef _ -> []
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
  let attrs = forGenAttrs (gdAttrs gen)
  let bargs = forGenBinderArgs (gdDom gen)
  let (ins, d0) = allocPorts dom (emptyDiagram mode [])
  let (outs, d1) = allocPorts cod d0
  d2 <- addEdgePayload (PGen (gdName gen) attrs bargs) ins outs d1
  let d3 = d2 { dIn = ins, dOut = outs }
  validateDiagram d3
  pure d3
  where
    forGenAttrs fields =
      M.fromList
        [ (fieldName, ATVar (AttrVar ("for_gen_" <> fieldName) fieldSort))
        | (fieldName, fieldSort) <- fields
        ]

    forGenBinderArgs domShapes =
      [ BAMeta (BinderMetaVar ("for_gen_b" <> T.pack (show i)))
      | (i, _) <- zip [0 :: Int ..] [ () | InBinder _ <- domShapes ]
      ]

    allocPorts [] diag = ([], diag)
    allocPorts (ty:rest) diag =
      let (pid, diag1) = freshPort ty diag
          (pids, diag2) = allocPorts rest diag1
       in (pid : pids, diag2)

elabGenAttrs :: Doctrine -> GenDecl -> Maybe [RawAttrArg] -> Either Text AttrMap
elabGenAttrs doc gen mArgs =
  case gdAttrs gen of
    [] ->
      case mArgs of
        Nothing -> Right M.empty
        Just _ -> Left "generator does not accept attribute arguments"
    fields -> do
      args <- maybe (Left "missing generator attribute arguments") Right mArgs
      normalized <- normalizeAttrArgs fields args
      (attrs, _) <- foldM elabOne (M.empty, M.empty) normalized
      Right attrs
  where
    elabOne (attrs, varSorts) (fieldName, fieldSort, rawTerm) = do
      (term, varSorts') <- elabRawAttrTerm doc fieldSort varSorts rawTerm
      Right (M.insert fieldName term attrs, varSorts')

normalizeAttrArgs :: [(AttrName, AttrSort)] -> [RawAttrArg] -> Either Text [(AttrName, AttrSort, RawAttrTerm)]
normalizeAttrArgs fields args =
  case (namedArgs, positionalArgs) of
    (_:_, _:_) -> Left "generator attribute arguments must be either all named or all positional"
    (_:_, []) -> normalizeNamed namedArgs
    ([], _) -> normalizePos positionalArgs
  where
    namedArgs = [ (name, term) | RAName name term <- args ]
    positionalArgs = [ term | RAPos term <- args ]
    fieldNames = map fst fields
    normalizeNamed named = do
      ensureDistinct "duplicate generator attribute argument" (map fst named)
      if length named /= length fields
        then Left "generator attribute argument mismatch"
        else Right ()
      if S.fromList (map fst named) == S.fromList fieldNames
        then Right ()
        else Left "generator attribute arguments must cover exactly the declared fields"
      let namedMap = M.fromList named
      traverse
        (\(fieldName, fieldSort) ->
          case M.lookup fieldName namedMap of
            Nothing -> Left "missing generator attribute argument"
            Just term -> Right (fieldName, fieldSort, term))
        fields
    normalizePos positional =
      if length positional /= length fields
        then Left "generator attribute argument mismatch"
        else Right [ (fieldName, fieldSort, term) | ((fieldName, fieldSort), term) <- zip fields positional ]

ensureDistinct :: Ord a => Text -> [a] -> Either Text ()
ensureDistinct label names =
  let set = S.fromList names
   in if S.size set == length names then Right () else Left label

elabRawAttrTerm
  :: Doctrine
  -> AttrSort
  -> M.Map Text AttrSort
  -> RawAttrTerm
  -> Either Text (AttrTerm, M.Map Text AttrSort)
elabRawAttrTerm doc expectedSort varSorts rawTerm =
  case rawTerm of
    RATVar name ->
      case M.lookup name varSorts of
        Nothing ->
          Right (ATVar (AttrVar name expectedSort), M.insert name expectedSort varSorts)
        Just sortName ->
          if sortName == expectedSort
            then Right (ATVar (AttrVar name expectedSort), varSorts)
            else Left "attribute variable used with conflicting sorts"
    RATInt n -> do
      ensureLiteralKind LKInt
      Right (ATLit (ALInt n), varSorts)
    RATString s -> do
      ensureLiteralKind LKString
      Right (ATLit (ALString s), varSorts)
    RATBool b -> do
      ensureLiteralKind LKBool
      Right (ATLit (ALBool b), varSorts)
  where
    ensureLiteralKind kind = do
      decl <-
        case M.lookup expectedSort (dAttrSorts doc) of
          Nothing -> Left "unknown attribute sort"
          Just d -> Right d
      case asLitKind decl of
        Just allowed | allowed == kind -> Right ()
        _ -> Left "attribute sort does not admit this literal kind"

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

freshTySubst :: Doctrine -> [TmVar] -> Fresh (M.Map TmVar Obj)
freshTySubst doc vars = do
  pairs <- mapM (freshTyVar doc) vars
  pure (M.fromList pairs)

freshTmSubst :: TypeTheory -> [Obj] -> [TmVar] -> Fresh (M.Map TmVar TermDiagram)
freshTmSubst ttDoc tmCtx vars = do
  pairs <- mapM (freshTmVar ttDoc tmCtx) vars
  pure (M.fromList pairs)

extractFreshTyVars :: [TmVar] -> M.Map TmVar Obj -> Either Text [TmVar]
extractFreshTyVars vars subst =
  mapM lookupVar vars
  where
    lookupVar v =
      case M.lookup v subst of
        Just (OVar v') -> Right v'
        _ -> Left "internal error: expected fresh type variable"

extractFreshTmVars :: [TmVar] -> M.Map TmVar TermDiagram -> Either Text [TmVar]
extractFreshTmVars vars subst =
  mapM lookupVar vars
  where
    lookupVar v =
      case M.lookup v subst of
        Just tm ->
          case metaOnly tm of
            Just v' -> Right v'
            Nothing -> Left "internal error: expected fresh term variable"
        _ -> Left "internal error: expected fresh term variable"

    metaOnly (TermDiagram diag) =
      case (IM.elems (dEdges diag), dOut diag) of
        ([edge], [outBoundary]) ->
          case (ePayload edge, eOuts edge) of
            (PTmMeta v, [outPid]) | outPid == outBoundary -> Just v
            _ -> Nothing
        _ -> Nothing

freshTyVar :: Doctrine -> TmVar -> Fresh (TmVar, Obj)
freshTyVar doc v = do
  n <- freshInt
  let name = tmvName v <> T.pack ("#" <> show n)
  let fresh = v { tmvName = name }
  ownerMode <- liftEither (ownerModeForTypeMeta doc v)
  pure (v, Obj { objOwnerMode = ownerMode, objCode = CTMeta fresh })

freshTmVar :: TypeTheory -> [Obj] -> TmVar -> Fresh (TmVar, TermDiagram)
freshTmVar ttDoc tmCtx v = do
  n <- freshInt
  let name = tmvName v <> T.pack ("#" <> show n)
  let fresh =
        TmVar
          { tmvName = name
          , tmvSort = tmvSort v
          , tmvScope = max (tmvScope v) (length (modeCtxGlobals tmCtx (objOwnerMode (tmvSort v))))
          , tmvOwnerMode = Nothing
          }
  tm <- liftEither (termExprToDiagramChecked ttDoc tmCtx (tmvSort fresh) (TMMeta fresh (defaultMetaArgs tmCtx fresh)))
  pure (v, tm)

freshInt :: Fresh Int
freshInt = Fresh (\n -> Right (n, n + 1))

liftEither :: Either Text a -> Fresh a
liftEither (Left err) = Fresh (\_ -> Left err)
liftEither (Right a) = pure a
