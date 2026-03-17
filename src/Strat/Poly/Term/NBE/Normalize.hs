{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.Poly.Term.NBE.Normalize
  ( normalizeDiagramDefEq
  , normalizeDiagramDefEqWithStep
  , validateDiagramDefEq
  , normalizeRuleDiagramDefEq
  , validateRuleDiagramDefEq
  ) where

import Control.Monad (foldM)
import Data.Maybe (isJust)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Alpha (freshenTmHeadSigAgainstWithMaps)
import Strat.Poly.DiagramBuild
  ( allocPorts
  , emitGenNode
  , finalizeSingleOutputDiagram
  , emitLiteralNode
  , emitMetaNode
  , emitSpliceNode
  )
import Strat.Poly.Literal (Literal)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.ModeSyntax (ModExpr(..))
import Strat.Poly.Graph
  ( Diagram(..)
  , PortId
  , Edge(..)
  , EdgePayload(..)
  , BinderMetaVar
  , BinderArg(..)
  , canonDiagramRaw
  , diagramPortObj
  , emptyDiagram
  , mergePorts
  , shiftDiagram
  , unPortId
  , unionDisjointIntMap
  , validateDiagram
  )
import Strat.Poly.Obj
  ( Obj(..)
  , ObjRef(..)
  , TermDiagram(..)
  , TmVar(..)
  , modeCtx
  , modeCtxGlobals
  , CodeArg(..)
  , CodeTerm(..)
  , defaultMetaArgs
  , freeVarsObj
  , objOwnerMode
  , sameTmVarId
  )
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Subst (applySubstDiagramWith, bindHeadSubst, mkSubst)
import Strat.Poly.Term.AST (TermBinderArg(..), TermExpr(..), TermHeadArg(..))
import Strat.Poly.Term.GraphRead (TermPortReader(..), readTermOutput)
import Strat.Poly.Term.RuleDiagram (expandSplices)
import qualified Strat.Poly.Term.RewriteSystem as RS
import Strat.Poly.TermExpr
  ( TermConvEnv(..)
  , applyHeadSubstObj
  , instantiateHostBoundObj
  , normalizeCtxStructurally
  , normalizeCtxStructurallyWithPrefix
  , termSubstOps
  , validateDefEqGraph
  )
import Strat.Poly.Tele (GenParam(..))
import Strat.Poly.Traversal (traverseDiagram)
import Strat.Poly.TypeTheory
  ( BuiltinHeads(..)
  , BinderSig(..)
  , DefFragment(..)
  , ExtensionalBuiltin(..)
  , EliminatorBuiltin(..)
  , BranchInputSource(..)
  , ElimBranchBuiltin(..)
  , InductiveElimBuiltin(..)
  , RecursiveHeadArgSource(..)
  , FunctionBuiltin(..)
  , TmHeadSig(..)
  , TypeTheory
  , defFragmentForMode
  , lookupTmHeadSig
  )

data BTm = BTm
  { btSort :: Obj
  , btExpr :: BTmExpr
  } deriving (Eq, Show)

data BTmHeadArg
  = BHAObj Obj
  | BHATm BTm
  deriving (Eq, Show)

data BTmBinderArg
  = BBABody Diagram
  | BBAHole BinderMetaVar
  deriving (Eq, Show)

data BTmExpr
  = BVar Int
  | BMeta TmVar [Int]
  | BGen GenName [BTmHeadArg] [BTm]
  | BBind GenName [BTmHeadArg] [BTm] [BTmBinderArg]
  | BResidual Diagram
  | BSplice BinderMetaVar ModExpr [BTm]
  | BLit Literal
  | BLam [BTmHeadArg] BTm
  | BApp [BTmHeadArg] BTm BTm
  deriving (Eq, Show)

data Val = Val
  { valSort :: Obj
  , valExpr :: ValExpr
  }

data ValExpr
  = VLam [ValHeadArg] (Val -> Either Text Val)
  | VLit Literal
  | VNeu Neu

data ValHeadArg
  = VHAObj Obj
  | VHATm Val

data ValBinderArg
  = VBABody Diagram
  | VBAHole BinderMetaVar

data BinderClosure = BinderClosure
  { bcRawBody :: Diagram
  , bcSlotTemplate :: BinderSig
  , bcOuterSortsOldToNew :: [Obj]
  , bcOuterEnv :: [Val]
  }

data ElimArg
  = ElimHole
  | ElimVal Val

data ElimFrame
  = AppFrame [ValHeadArg] Val Obj Obj
  | BuiltinElimFrame GenName [ValHeadArg] [ElimArg] [BinderClosure] Obj

data Neu
  = NVar Int Obj
  | NMeta TmVar [Val]
  | NGen GenName [ValHeadArg] [Val] Obj
  | NBind GenName [ValHeadArg] [Val] [ValBinderArg] Obj
  | NDiagram Diagram Obj
  | NSplice BinderMetaVar ModExpr [Val] Obj
  | NElim Neu ElimFrame

frameResultSort :: ElimFrame -> Obj
frameResultSort frame =
  case frame of
    AppFrame _ _ _ codTy -> codTy
    BuiltinElimFrame _ _ _ _ sortTy -> sortTy

neutralSort :: Neu -> Obj
neutralSort neu =
  case neu of
    NVar _ sortTy -> sortTy
    NMeta v _ -> tmvSort v
    NGen _ _ _ sortTy -> sortTy
    NBind _ _ _ _ sortTy -> sortTy
    NDiagram _ sortTy -> sortTy
    NSplice _ _ _ sortTy -> sortTy
    NElim _ frame -> frameResultSort frame

neutralValue :: Neu -> Val
neutralValue neu =
  Val
    { valSort = neutralSort neu
    , valExpr = VNeu neu
    }

data RuleSubst = RuleSubst
  { rsBoundVals :: M.Map Int Val
  , rsHeadSubst :: M.Map TmVar CodeArg
  , rsBinderVals :: M.Map BinderMetaVar RuleBinderCapture
  }

data RuleBinderCapture = RuleBinderCapture
  { rbcSlot :: BinderSig
  , rbcValue :: RuleBinderCaptureValue
  }

data RuleBinderCaptureValue
  = RBCConcrete Diagram
  | RBCSymbolic BinderMetaVar
  deriving (Eq, Show)

emptyRuleSubst :: RuleSubst
emptyRuleSubst =
  RuleSubst
    { rsBoundVals = M.empty
    , rsHeadSubst = M.empty
    , rsBinderVals = M.empty
    }

type StructuralStep = Diagram -> Either Text (Maybe Diagram)

noStructuralStep :: StructuralStep
noStructuralStep _ = Right Nothing

normalizeDiagramDefEq
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermDiagram
normalizeDiagramDefEq fragment tt convEnv tmCtx expectedSort src = do
  normalizeDiagramDefEqWithStep fragment tt convEnv tmCtx expectedSort noStructuralStep src

normalizeDiagramDefEqWithStep
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Obj
  -> StructuralStep
  -> Diagram
  -> Either Text TermDiagram
normalizeDiagramDefEqWithStep fragment tt convEnv tmCtx expectedSort structuralStep src = do
  case dOut src of
    [_] -> pure ()
    _ -> Left "defeq: term diagram must have exactly one output"
  let nIn = length (dIn src)
  let modeInputsAll = modeCtx tmCtx (dMode src)
  if nIn <= length modeInputsAll
    then pure ()
    else Left "defeq: boundary input prefix exceeds mode-local context"
  let boundarySorts = map snd (take nIn modeInputsAll)
  normalizeDiagramDefEqAgainstWithStep fragment tt convEnv tmCtx boundarySorts expectedSort structuralStep src

validateDiagramDefEq
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text ()
validateDiagramDefEq fragment tt convEnv tmCtx expectedSort src = do
  case dOut src of
    [_] -> pure ()
    _ -> Left "defeq: term diagram must have exactly one output"
  let modeInputsAll = modeCtx tmCtx (dMode src)
      nIn = length (dIn src)
  if nIn <= length modeInputsAll
    then pure ()
    else Left "defeq: boundary input prefix exceeds mode-local context"
  let boundarySorts = map snd (take nIn modeInputsAll)
  validateDiagramDefEqAgainst fragment tt convEnv boundarySorts expectedSort src

normalizeRuleDiagramDefEq
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermDiagram
normalizeRuleDiagramDefEq fragment tt convEnv tmCtx boundarySorts expectedSort src =
  normalizeDiagramDefEqAgainst fragment tt convEnv tmCtx boundarySorts expectedSort src

validateRuleDiagramDefEq
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text ()
validateRuleDiagramDefEq fragment tt convEnv boundarySorts expectedSort src =
  validateDiagramDefEqAgainst fragment tt convEnv boundarySorts expectedSort src

normalizeDiagramDefEqAgainst
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermDiagram
normalizeDiagramDefEqAgainst fragment tt convEnv tmCtx boundarySorts expectedSort src = do
  normalizeDiagramDefEqAgainstWithStep fragment tt convEnv tmCtx boundarySorts expectedSort noStructuralStep src

normalizeDiagramDefEqAgainstWithStep
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> [Obj]
  -> Obj
  -> StructuralStep
  -> Diagram
  -> Either Text TermDiagram
normalizeDiagramDefEqAgainstWithStep fragment tt convEnv tmCtx boundarySorts expectedSort structuralStep src0 =
  loop S.empty src0
  where
    attemptRound src = do
      let nIn = length (dIn src)
      if nIn <= length boundarySorts
        then
          normalizeDiagramDefEqRoundAgainst
            fragment
            tt
            convEnv
            tmCtx
            (take nIn boundarySorts)
            expectedSort
            src
        else
          Left "defeq: normalized term requires larger boundary context prefix than available"

    loop seen current0 = do
      current <- canonDiagramRaw current0
      if current `S.member` seen
        then Left "defeq: computational structural normalization encountered a rewrite cycle"
        else do
          let seen' = S.insert current seen
          structuralRes <- structuralStep current
          nextStructural <-
            case structuralRes of
              Nothing -> Right current
              Just diag -> canonDiagramRaw diag
          case attemptRound nextStructural of
            Right out ->
              let next = unTerm out
                  progressed = isJust structuralRes || next /= current
               in if progressed
                    then loop seen' next
                    else Right out
            Left err ->
              case structuralRes of
                Just _ -> loop seen' nextStructural
                Nothing -> Left err

normalizeDiagramDefEqRoundAgainst
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermDiagram
normalizeDiagramDefEqRoundAgainst fragment tt convEnv tmCtx boundarySorts expectedSort src = do
  validateDiagramDefEqAgainst fragment tt convEnv boundarySorts expectedSort src
  let nIn = length boundarySorts
  tm <- diagramToBTm fragment tt convEnv src [nIn - 1, nIn - 2 .. 0] boundarySorts expectedSort
  let lvl0 = nIn
  env <- mkInitialEnv lvl0 boundarySorts
  val <- evalBTm fragment tt convEnv tmCtx env tm
  nf <- reify fragment tt convEnv tmCtx lvl0 expectedSort val
  needed <- requiredTopPrefix nf
  if needed <= length boundarySorts
    then pure ()
    else Left "defeq: normalized term requires larger boundary context prefix than available"
  out <- btmToDiagram tt fragment tmCtx expectedSort (take needed boundarySorts) nf
  validateDiagram out
  outCanon <- canonDiagramRaw out
  validateDiagram outCanon
  pure (TermDiagram outCanon)

validateDiagramDefEqAgainst
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text ()
validateDiagramDefEqAgainst fragment tt convEnv boundarySorts expectedSort src = do
  validateDefEqGraph src
  case dOut src of
    [_] -> pure ()
    _ -> Left "defeq: term diagram must have exactly one output"
  if length (dIn src) == length boundarySorts
    then pure ()
    else Left "defeq: boundary input arity does not match expected boundary context"
  mapM_ checkBoundaryType (zip boundarySorts (dIn src))
  _ <- diagramToBTm fragment tt convEnv src [length boundarySorts - 1, length boundarySorts - 2 .. 0] boundarySorts expectedSort
  pure ()
  where
    checkBoundaryType (expectedTy, pid) = do
      actualTy <- requirePortSort src "NbE: missing boundary input sort" pid
      ok <- tcSortEq convEnv boundarySorts actualTy expectedTy
      if ok
        then pure ()
        else
          Left
            ( "defeq: boundary input sort mismatch (expected "
                <> T.pack (show expectedTy)
                <> ", got "
                <> T.pack (show actualTy)
                <> ")"
            )

diagramToBTm :: DefFragment -> TypeTheory -> TermConvEnv -> Diagram -> [Int] -> [Obj] -> Obj -> Either Text BTm
diagramToBTm fragment tt convEnv diag boundaryVars boundarySorts expectedSort =
  diagramToBTmWithAmbient
    fragment
    tt
    convEnv
    diag
    boundaryVars
    []
    boundarySorts
    expectedSort
    (\_ _ _ _ -> Right Nothing)

diagramToBTmWithAmbient
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> Diagram
  -> [Int]
  -> [Int]
  -> [Obj]
  -> Obj
  -> ([Obj] -> Obj -> TmVar -> [PortId] -> Either Text (Maybe BTm))
  -> Either Text BTm
diagramToBTmWithAmbient fragment tt convEnv diag boundaryVars ambientTmCtxVars boundarySorts expectedSort resolveMeta =
  diagramToBTmWith
    fragment
    tt
    convEnv
    diag
    boundaryVars
    ambientTmCtxVars
    boundarySorts
    expectedSort
    resolveMeta

diagramToBTmWith
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> Diagram
  -> [Int]
  -> [Int]
  -> [Obj]
  -> Obj
  -> ([Obj] -> Obj -> TmVar -> [PortId] -> Either Text (Maybe BTm))
  -> Either Text BTm
diagramToBTmWith fragment tt convEnv diag boundaryVars ambientTmCtxVars boundarySorts expectedSort resolveMeta = do
  validateDiagram diag
  if length boundarySorts == length (dIn diag)
    then pure ()
    else Left "NbE: explicit boundary context arity does not match diagram inputs"
  let reader = mkReader boundarySorts
  case dOut diag of
    [out] -> do
      outTy <- requirePortSort diag "NbE: missing output sort" out
      sortMatches <- tcSortEq convEnv boundarySorts outTy expectedSort
      if sortMatches
        then
          if hasImmediateStructuralPayload diag
            then do
              residual <- normalizeResidualDiagramPayloads tt convEnv diag
              pure BTm { btSort = expectedSort, btExpr = BResidual residual }
            else readTermOutput reader diag expectedSort
        else
          Left
            ( "NbE: output sort mismatch (expected "
                <> T.pack (show expectedSort)
                <> ", got "
                <> T.pack (show outTy)
                <> ")"
            )
    _ -> Left "NbE: term diagram must have exactly one output"
  where
    inMap = M.fromList (zip (dIn diag) [0 :: Int ..])

    mkReader ctxSorts =
      TermPortReader
        { tprBoundaryLookup = \pid -> M.lookup pid inMap
        , tprOnBoundary = \currentSort localIx pid ->
            case nth boundaryVars localIx of
              Nothing -> Left "NbE: invalid boundary-variable mapping"
              Just idx -> do
                sortTy <- requirePortSort diag "NbE: missing boundary sort" pid
                sortMatches <- tcSortEq convEnv ctxSorts sortTy currentSort
                if sortMatches
                  then pure BTm { btSort = sortTy, btExpr = BVar idx }
                  else
                    Left
                      ( "NbE: boundary sort mismatch (expected "
                          <> T.pack (show currentSort)
                          <> ", got "
                          <> T.pack (show sortTy)
                          <> ")"
                      )
        , tprOnEdge = \recur currentSort pid edge ->
            case ePayload edge of
              PGen _ args bargs ->
                if isLamPrimitive pid edge bargs
                  then parseLam boundarySorts currentSort pid edge args bargs
                  else
                    if isAppPrimitive pid edge bargs
                      then parseApp boundarySorts recur currentSort pid edge args
                      else parseResidualHead boundarySorts recur currentSort pid edge args bargs
              PProvider _ ->
                Left "NbE: provider nodes are unsupported in definitional normalization"
              PModuleRef _ ->
                Left "NbE: module-reference nodes are unsupported in definitional normalization"
              PTmMeta v -> do
                resolvedMeta <- resolveMeta ctxSorts currentSort v (eIns edge)
                case resolvedMeta of
                  Just tm -> pure tm
                  Nothing -> do
                    sortTy <- requirePortSort diag "NbE: missing PTmMeta output sort" pid
                    sortMatches <- tcSortEq convEnv ctxSorts sortTy currentSort
                    if sortMatches
                      then do
                        let v' = v { tmvSort = sortTy }
                        metaArgs <- mapM boundaryVarIndex (eIns edge)
                        pure BTm { btSort = sortTy, btExpr = BMeta v' metaArgs }
                      else
                        Left "NbE: metavariable output sort mismatch"
              PTmLit lit -> do
                sortTy <- requirePortSort diag "NbE: missing literal output sort" pid
                sortMatches <- tcSortEq convEnv ctxSorts sortTy currentSort
                if sortMatches
                  then pure BTm { btSort = sortTy, btExpr = BLit lit }
                  else Left "NbE: literal output sort mismatch"
              PInternalDrop ->
                Left "NbE: reachable PInternalDrop is unsupported in NbE term normalization"
              PBox _ _ ->
                Left "NbE: box nodes are unsupported in NbE definitional normalization"
              PFeedback _ ->
                Left "NbE: feedback nodes are unsupported in NbE definitional normalization"
              PSplice hole me ->
                case eOuts edge of
                  [outPid]
                    | outPid == pid -> do
                        args <- mapM (readInputTerm recur) (eIns edge)
                        pure BTm { btSort = currentSort, btExpr = BSplice hole me args }
                  _ ->
                    Left "NbE: splice node must have exactly one output"
        , tprSingleOutputErr = "NbE: term diagram must have exactly one output"
        , tprCycleErr = "NbE: cycle detected in term diagram"
        , tprMissingProducerErr = "NbE: missing producer edge"
        }

    boundaryVarIndex pid =
      case M.lookup pid inMap of
        Just local ->
          case nth boundaryVars local of
            Just idx -> Right idx
            Nothing -> Left "NbE: boundary-variable mapping failure"
        Nothing ->
          Left "NbE: PTmMeta inputs must connect to boundary ports"

    isLamPrimitive pid edge bargs =
      case functionBuiltin fragment of
        Just fb ->
          case (ePayload edge, eIns edge, eOuts edge, bargs) of
            (PGen g _ _, [], [outPid], [BAConcrete _]) ->
              g == fbLamGen fb && outPid == pid
            _ ->
              False
        Nothing ->
          False

    isAppPrimitive pid edge bargs =
      case functionBuiltin fragment of
        Just fb ->
          case (ePayload edge, eIns edge, eOuts edge, bargs) of
            (PGen g _ _, [_fIn, _aIn], [outPid], []) ->
              g == fbAppGen fb && outPid == pid
            _ ->
              False
        Nothing ->
          False

    parseLam ctxSorts currentSort pid edge args bargs = do
      case (eIns edge, eOuts edge, bargs) of
        ([], [outPid], [BAConcrete bodyDiag])
          | outPid == pid -> do
              headArgs <- mapM (storedArgToBTm boundaryVars) args
              lamSort <- requirePortSort diag "NbE: missing lambda output sort" outPid
              sortMatches <- tcSortEq convEnv ctxSorts lamSort currentSort
              if sortMatches
                then Right ()
                else Left "NbE: lambda output sort mismatch"
              (domTy, codTy) <-
                case splitArr fragment lamSort of
                  Just parts -> Right parts
                  Nothing ->
                    Left
                      ( "NbE: lambda output is not an Arr type: "
                          <> T.pack (show lamSort)
                      )
              let outer = map (+ 1) boundaryVars
              let bodyAvailable = 0 : outer
              let bodyInCount = length (dIn bodyDiag)
              if bodyInCount >= 1 && bodyInCount <= length bodyAvailable
                then Right ()
                else Left "NbE: lambda binder body must expose bound var first and then an outer-prefix"
              firstBodyIn <-
                case dIn bodyDiag of
                  (p:_) -> Right p
                  [] -> Left "NbE: lambda binder body must have at least one input"
              firstBodyTy <- requirePortSort bodyDiag "NbE: lambda binder body missing bound-variable sort" firstBodyIn
              let bodyBoundaryVars = take bodyInCount bodyAvailable
              bodyInSorts <- mapM (requirePortSort bodyDiag "NbE: missing boundary input sort") (dIn bodyDiag)
              bodyDomMatches <- tcSortEq convEnv bodyInSorts firstBodyTy domTy
              if bodyDomMatches
                then Right ()
                else Left "NbE: lambda binder body bound-variable sort mismatch"
              body <- diagramToBTm fragment tt convEnv bodyDiag bodyBoundaryVars bodyInSorts codTy
              pure BTm { btSort = lamSort, btExpr = BLam headArgs body }
        _ ->
          Left "NbE: lam node must have no plain inputs, one output, and one concrete binder body"

    parseApp ctxSorts recur currentSort pid edge args = do
      case (eIns edge, eOuts edge) of
        ([fIn, aIn], [outPid])
          | outPid == pid -> do
              headArgs <- mapM (storedArgToBTm boundaryVars) args
              fTm <- readInputTerm recur fIn
              outTy <- requirePortSort diag "NbE: missing app output sort" outPid
              outMatches <- tcSortEq convEnv ctxSorts outTy currentSort
              if outMatches
                then Right ()
                else Left "NbE: app output sort mismatch"
              case splitArr fragment (btSort fTm) of
                Just (domTy, codTy) -> do
                  aTm <- recur domTy aIn
                  domMatches <- tcSortEq convEnv ctxSorts domTy (btSort aTm)
                  codMatches <- tcSortEq convEnv ctxSorts codTy outTy
                  if domMatches && codMatches
                    then pure BTm { btSort = outTy, btExpr = BApp headArgs fTm aTm }
                    else Left "NbE: app node type mismatch against Arr(domain, codomain)"
                Nothing ->
                  Left "NbE: app function input does not have Arr type"
        _ ->
          Left "NbE: app node must have exactly two inputs, one output, and no binder args"

    parseResidualHead ctxSorts recur currentSort pid edge args bargs = do
      case eOuts edge of
        [outPid]
          | outPid == pid -> do
              case lookupHeadSigByShape (payloadGen edge) args (length (eIns edge)) (length bargs) of
                Right sig0 -> do
                  let used = S.unions (map freeVarsObj (currentSort : ctxSorts))
                  let (sig, _, _) = freshenTmHeadSigAgainstWithMaps used sig0
                  (headArgs, substAfterParams) <- rebuildStoredArgs ctxSorts sig args
                  inputArgs <- rebuildInputs ctxSorts recur substAfterParams (zip (thsInputs sig) (eIns edge))
                  binderArgs <- mapM residualBinderArg bargs
                  sortTy0 <- applyHeadSubstObj tt convEnv ctxSorts substAfterParams (thsRes sig)
                  sortTy <- tcNormalizeSort convEnv ctxSorts sortTy0
                  sortMatches <- tcSortEq convEnv ctxSorts sortTy currentSort
                  if sortMatches
                    then Right ()
                    else Left "NbE: residual head output sort mismatch"
                  pure
                    BTm
                      { btSort = sortTy
                      , btExpr =
                          if null bargs
                            then BGen (payloadGen edge) headArgs inputArgs
                            else BBind (payloadGen edge) headArgs inputArgs binderArgs
                      }
                Left err -> Left err
        _ ->
          Left
            ( "NbE: residual term head "
                <> T.pack (show (payloadGen edge))
                <> " must have exactly one output (got "
                <> T.pack (show (length (eOuts edge)))
                <> ")"
            )

    lookupHeadSigByShape gen args inputCount binderCount =
      case M.lookup gen (dfHeads fragment) of
        Just sig
          | length (thsParams sig) + length (thsInputs sig) == length args + inputCount
              && length (thsBinders sig) == binderCount ->
              Right sig
          | otherwise ->
              Left "NbE: residual head arity mismatch"
        Nothing ->
          Left "NbE: unknown residual term head"

    readInputTerm recur pid = do
      inputSort <- requirePortSort diag "NbE: missing input sort" pid
      recur inputSort pid

    rebuildStoredArgs ctxSorts sig args =
      foldM
        stepStoredArg
        ([], M.empty)
        (zip (thsParams sig) args)
      where
        stepStoredArg (acc, substAcc) (param, arg) =
          case (param, arg) of
            (GP_Ty v, CAObj obj) -> do
              obj' <- tcNormalizeSort convEnv ctxSorts obj
              subst' <- bindHeadSubst v (CAObj obj') substAcc
              pure (acc <> [BHAObj obj'], subst')
            (GP_Ty _, CATm _) ->
              Left "NbE: expected object-valued stored arg"
            (GP_Tm v, CATm tmArg) -> do
              expectedArgSort0 <- applyHeadSubstObj tt convEnv ctxSorts substAcc (tmvSort v)
              expectedArgSort <- tcNormalizeSort convEnv ctxSorts expectedArgSort0
              tmArg' <- storedArgToBTmExpected boundaryVars expectedArgSort tmArg
              subst' <- bindHeadSubst v (CATm tmArg) substAcc
              pure (acc <> [BHATm tmArg'], subst')
            (GP_Tm _, CAObj _) ->
              Left "NbE: expected term-valued stored arg"

    rebuildInputs ctxSorts recur substAfterParams inputs =
      foldM
        (\acc (argSort, inputPid) -> do
          expectedArgSort0 <- applyHeadSubstObj tt convEnv ctxSorts substAfterParams argSort
          expectedArgSort <- tcNormalizeSort convEnv ctxSorts expectedArgSort0
          argExpr <- recur expectedArgSort inputPid
          pure (acc <> [argExpr]))
        []
        inputs

    payloadGen edge =
      case ePayload edge of
        PGen g _ _ -> g
        _ -> error "NbE internal: residual payload expected generator head"

    residualBinderArg barg =
      case barg of
        BAConcrete inner ->
          Right (BBABody inner)
        BAMeta hole ->
          Right (BBAHole hole)

    storedArgToBTm outerBoundaryVars arg =
      case arg of
        CAObj obj -> Right (BHAObj obj)
        CATm (TermDiagram inner) -> do
          sortTy <- termDiagramSort inner
          tm <- storedArgDiagramToBTm outerBoundaryVars sortTy inner
          Right (BHATm tm)

    storedArgToBTmExpected outerBoundaryVars sortTy (TermDiagram inner) =
      storedArgDiagramToBTm outerBoundaryVars sortTy inner

    storedArgDiagramToBTm outerBoundaryVars sortTy inner = do
      let innerGlobals = modeCtxGlobals (dTmCtx inner) (objOwnerMode sortTy)
          useAmbient =
            not (null innerGlobals)
              && length innerGlobals == length (dIn inner)
              && all (\g -> g >= 0 && g < length ambientTmCtxVars) innerGlobals
          innerBoundaryVars =
            if useAmbient
              then map (ambientTmCtxVars !!) innerGlobals
              else take (length (dIn inner)) outerBoundaryVars
      innerBoundarySorts <- mapM (requirePortSort inner "NbE: missing stored term-arg boundary sort") (dIn inner)
      let argFragment =
            case defFragmentForMode tt (objOwnerMode sortTy) of
              Just fragment' -> fragment'
              Nothing -> fragment
      diagramToBTmWithAmbient argFragment tt convEnv inner innerBoundaryVars ambientTmCtxVars innerBoundarySorts sortTy (\_ _ _ _ -> Right Nothing)

    termDiagramSort inner =
      case dOut inner of
        [outPid] -> requirePortSort inner "NbE: missing stored term-arg output sort" outPid
        _ -> Left "NbE: stored term argument must have exactly one output"

evalBTm :: DefFragment -> TypeTheory -> TermConvEnv -> [Obj] -> [Val] -> BTm -> Either Text Val
evalBTm fragment tt convEnv tmCtx env tm =
  case btExpr tm of
    BVar i ->
      case nth env i of
        Just v -> Right v
        Nothing -> Left "NbE: de Bruijn variable out of scope during evaluation"
    BMeta v args -> do
      argVals <- mapM lookupArg args
      Right
        Val
          { valSort = btSort tm
          , valExpr = VNeu (NMeta v argVals)
          }
    BGen g headArgs args -> do
      headVals <- mapM evalHeadArg headArgs
      vals <- mapM (evalBTm fragment tt convEnv tmCtx env) args
      evalHeadApplication fragment tt convEnv tmCtx (length env) (btSort tm) g headVals vals
    BBind g headArgs args binderArgs -> do
      headVals <- mapM evalHeadArg headArgs
      vals <- mapM (evalBTm fragment tt convEnv tmCtx env) args
      evalBinderHeadApplication
        fragment
        tt
        convEnv
        tmCtx
        (length env)
        (btSort tm)
        g
        headVals
        vals
        (map evalBinderArg binderArgs)
    BResidual residual ->
      Right
        Val
          { valSort = btSort tm
          , valExpr = VNeu (NDiagram residual (btSort tm))
          }
    BSplice hole me args -> do
      vals <- mapM (evalBTm fragment tt convEnv tmCtx env) args
      pure
        Val
          { valSort = btSort tm
          , valExpr = VNeu (NSplice hole me vals (btSort tm))
          }
    BLit lit ->
      Right
        Val
          { valSort = btSort tm
          , valExpr = VLit lit
          }
    BLam headArgs body -> do
      headVals <- mapM evalHeadArg headArgs
      Right
        Val
          { valSort = btSort tm
          , valExpr =
              VLam headVals
                ( \v ->
                    evalBTm fragment tt convEnv tmCtx (v : env) body
                )
          }
    BApp headArgs f a -> do
      headVals <- mapM evalHeadArg headArgs
      fV <- evalBTm fragment tt convEnv tmCtx env f
      aV <- evalBTm fragment tt convEnv tmCtx env a
      applyVal fragment convEnv tmCtx (Just headVals) fV aV
  where
    lookupArg i =
      case nth env i of
        Just v -> Right v
        Nothing -> Left "NbE: metavariable argument index out of scope during evaluation"

    evalHeadArg arg =
      case arg of
        BHAObj obj -> Right (VHAObj obj)
        BHATm tmArg -> VHATm <$> evalBTm fragment tt convEnv tmCtx env tmArg

    evalBinderArg barg =
      case barg of
        BBABody inner -> VBABody inner
        BBAHole hole -> VBAHole hole

evalHeadApplication
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> GenName
  -> [ValHeadArg]
  -> [Val]
  -> Either Text Val
evalHeadApplication fragment tt convEnv tmCtx lvl resultSort g headArgs args =
  case functionBuiltin fragment of
    Just fb
      | g == fbAppGen fb ->
          case args of
            [funVal, argVal] ->
              applyVal fragment convEnv tmCtx (Just headArgs) funVal argVal
            _ ->
              Left "defeq: builtin application head expects exactly two inputs"
    _ | Just builtin <- extensionalBuiltin fragment g ->
          evalBuiltinExtensional fragment tt convEnv tmCtx lvl resultSort g builtin headArgs args []
    _ | Just builtin <- eliminatorBuiltin fragment g ->
          evalBuiltinEliminator fragment tt convEnv tmCtx lvl resultSort g builtin headArgs args []
    _ ->
      tryRewriteHead fragment tt convEnv tmCtx lvl residual
  where
    residual =
      Val
        { valSort = resultSort
        , valExpr = VNeu (NGen g headArgs args resultSort)
        }

evalBinderHeadApplication
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> GenName
  -> [ValHeadArg]
  -> [Val]
  -> [ValBinderArg]
  -> Either Text Val
evalBinderHeadApplication fragment tt convEnv tmCtx lvl resultSort g headArgs args binderArgs =
  case functionBuiltin fragment of
    Just fb
      | g == fbLamGen fb ->
          if allConcreteBinderArgs binderArgs
            then evalBuiltinLam fragment tt convEnv tmCtx lvl resultSort headArgs args binderArgs
            else tryRewriteHead fragment tt convEnv tmCtx lvl residual
    _ | Just builtin <- extensionalBuiltin fragment g ->
          evalBuiltinExtensional fragment tt convEnv tmCtx lvl resultSort g builtin headArgs args binderArgs
    _ | Just builtin <- eliminatorBuiltin fragment g ->
          if allConcreteBinderArgs binderArgs
            then evalBuiltinEliminator fragment tt convEnv tmCtx lvl resultSort g builtin headArgs args binderArgs
            else tryRewriteHead fragment tt convEnv tmCtx lvl residual
    _ ->
      tryRewriteHead fragment tt convEnv tmCtx lvl residual
  where
    residual =
      Val
        { valSort = resultSort
        , valExpr = VNeu (NBind g headArgs args binderArgs resultSort)
        }
    allConcreteBinderArgs =
      all
        ( \barg ->
            case barg of
              VBABody _ -> True
              VBAHole _ -> False
        )

evalBuiltinLam
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> [ValHeadArg]
  -> [Val]
  -> [ValBinderArg]
  -> Either Text Val
evalBuiltinLam fragment tt convEnv tmCtx lvl resultSort headArgs args binderArgs = do
  lamSort <- tcNormalizeSort convEnv tmCtx resultSort
  (domTy, codTy) <-
    case splitArr fragment lamSort of
      Just parts -> Right parts
      Nothing ->
        Left
          ( "defeq: builtin lambda head does not produce an Arr type: "
              <> T.pack (show lamSort)
          )
  bodyDiag <-
    case (args, binderArgs) of
      ([], [VBABody body]) -> Right body
      _ -> Left "defeq: builtin lambda head expects no plain inputs and exactly one concrete binder body"
  let modeInputsAll = modeCtx tmCtx (objOwnerMode lamSort)
  if lvl <= length modeInputsAll
    then Right ()
    else Left "defeq: builtin lambda RHS requires larger mode-local context prefix than available"
  let outerSortsOldToNew = map snd (take lvl modeInputsAll)
  body <- decodeBuiltinLamBody fragment tt convEnv [lvl - 1, lvl - 2 .. 0] outerSortsOldToNew lamSort domTy codTy bodyDiag
  outerEnv <- mkInitialEnv lvl outerSortsOldToNew
  pure
    Val
      { valSort = lamSort
      , valExpr = VLam headArgs (\v -> evalBTm fragment tt convEnv tmCtx (v : outerEnv) body)
      }

evalBuiltinExtensional
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> GenName
  -> ExtensionalBuiltin
  -> [ValHeadArg]
  -> [Val]
  -> [ValBinderArg]
  -> Either Text Val
evalBuiltinExtensional fragment tt convEnv tmCtx lvl resultSort g builtin headArgs args binderArgs =
  case builtin of
    BuiltinTransport ->
      evalBuiltinTransport fragment tt convEnv tmCtx lvl resultSort g headArgs args binderArgs

evalBuiltinEliminator
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> GenName
  -> EliminatorBuiltin
  -> [ValHeadArg]
  -> [Val]
  -> [ValBinderArg]
  -> Either Text Val
evalBuiltinEliminator fragment tt convEnv tmCtx lvl resultSort g builtin headArgs args binderArgs =
  case builtin of
    BuiltinInductiveElim elimBuiltin ->
      evalBuiltinInductiveElim fragment tt convEnv tmCtx lvl resultSort g elimBuiltin headArgs args binderArgs

evalBuiltinTransport
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> GenName
  -> [ValHeadArg]
  -> [Val]
  -> [ValBinderArg]
  -> Either Text Val
evalBuiltinTransport _fragment _tt convEnv tmCtx _lvl resultSort _g _headArgs args binderArgs =
  case (args, binderArgs) of
    ([argVal], []) -> do
      sortsAgree <- tcSortEq convEnv tmCtx (valSort argVal) resultSort
      if sortsAgree
        then Right argVal { valSort = resultSort }
        else
          Left
            ( "defeq: builtin transport head expects definitionally equal input/result sorts (input "
                <> T.pack (show (valSort argVal))
                <> ", result "
                <> T.pack (show resultSort)
                <> ")"
            )
    _ ->
      Left "defeq: builtin transport head expects exactly one plain input and no binder inputs"

evalBuiltinInductiveElim
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> GenName
  -> InductiveElimBuiltin
  -> [ValHeadArg]
  -> [Val]
  -> [ValBinderArg]
  -> Either Text Val
evalBuiltinInductiveElim fragment tt convEnv tmCtx lvl resultSort g elimBuiltin headArgs args binderArgs = do
  resultSort' <- tcNormalizeSort convEnv tmCtx resultSort
  (sig, headSubst) <- instantiateBuiltinHeadSig fragment tt convEnv tmCtx lvl resultSort' g headArgs
  if length args == length (thsInputs sig)
    then Right ()
    else Left "defeq: builtin fold head received a plain-input arity mismatch"
  if length binderArgs == length (thsBinders sig)
    then Right ()
    else Left "defeq: builtin fold head received a binder-input arity mismatch"
  closures <-
    mapM
      (uncurry (prepareBuiltinBinderClosure fragment tt convEnv tmCtx lvl))
      (zip (thsBinders sig) binderArgs)
  scrutineeVal <-
    case nth args (iebScrutineeIndex elimBuiltin) of
      Just val -> Right val
      Nothing -> Left "defeq: builtin fold head is missing its scrutinee argument"
  let evalAt currentHeadArgs currentHeadSubst currentArgs currentResultSort scrutinee =
        case valExpr scrutinee of
          VNeu neu ->
            case constructorFoldStep currentHeadArgs currentHeadSubst currentArgs currentResultSort neu of
              Just step ->
                step
              Nothing ->
                pure
                  ( neutralValue
                      ( NElim
                          neu
                          ( BuiltinElimFrame
                              g
                              currentHeadArgs
                              (headFrameArgs (iebScrutineeIndex elimBuiltin) currentArgs)
                              closures
                              currentResultSort
                          )
                      )
                  )
          _ ->
            Left "defeq: builtin fold head expects a neutral or constructor-headed scrutinee"

      constructorFoldStep currentHeadArgs currentHeadSubst currentArgs currentResultSort neu =
        case neu of
          NGen ctor ctorHeadArgs ctorArgs _
            | Just (branch, closure) <- lookupBranchClosure ctor ->
                Just (applyBranch currentHeadArgs currentHeadSubst currentArgs currentResultSort branch closure ctorHeadArgs ctorArgs)
          _ ->
            Nothing

      lookupBranchClosure ctor =
        let candidates = zip (iebBranches elimBuiltin) closures
         in case filter (\(branch, _) -> ebbCtorGen branch == ctor) candidates of
              [match] -> Just match
              _ -> Nothing

      applyBranch currentHeadArgs currentHeadSubst currentArgs currentResultSort branch closure ctorHeadArgs ctorArgsOldToNew = do
        branchTmCtxVals <-
          mapM
            (projectBranchSource currentHeadArgs currentArgs ctorHeadArgs ctorArgsOldToNew)
            (ebbTmCtxInputs branch)
        branchArgsOldToNew <-
          mapM
            (projectBranchSource currentHeadArgs currentArgs ctorHeadArgs ctorArgsOldToNew)
            (ebbInputs branch)
        applyBinderClosure fragment tt convEnv tmCtx currentHeadSubst closure branchTmCtxVals branchArgsOldToNew

      projectBranchSource currentHeadArgs currentArgs ctorHeadArgs ctorArgsOldToNew source =
        case source of
          BISOuterHeadTmParam i ->
            case nth currentHeadArgs i of
              Just (VHATm argVal) -> Right argVal
              Just (VHAObj _) -> Left "defeq: builtin eliminator branch expects a term-valued outer head parameter"
              Nothing -> Left "defeq: builtin eliminator branch refers to a missing outer head parameter"
          BISCtorHeadTmParam i ->
            case nth ctorHeadArgs i of
              Just (VHATm argVal) -> Right argVal
              Just (VHAObj _) -> Left "defeq: builtin eliminator branch expects a term-valued constructor head parameter"
              Nothing -> Left "defeq: builtin eliminator branch refers to a missing constructor head parameter"
          BISOuterInput i ->
            case nth currentArgs i of
              Just argVal -> Right argVal
              Nothing -> Left "defeq: builtin eliminator branch refers to a missing outer input"
          BISCtorField i ->
            case nth ctorArgsOldToNew i of
              Just argVal -> Right argVal
              Nothing -> Left "defeq: builtin eliminator branch refers to a missing constructor field"
          BISRecursiveResult i recursiveHeadArgs -> do
            argVal <-
              case nth ctorArgsOldToNew i of
                Just val -> Right val
                Nothing -> Left "defeq: builtin eliminator branch refers to a missing recursive constructor field"
            nextHeadArgs <- instantiateRecursiveHeadArgs currentHeadArgs ctorHeadArgs recursiveHeadArgs
            nextHeadSubst <- bindBuiltinHeadArgs fragment tt convEnv tmCtx lvl sig nextHeadArgs
            nextResultSort <- instantiateBuiltinResultSort tt convEnv tmCtx nextHeadSubst sig
            let recursiveArgs = replaceAt (iebScrutineeIndex elimBuiltin) argVal currentArgs
            evalAt nextHeadArgs nextHeadSubst recursiveArgs nextResultSort argVal
  evalAt headArgs headSubst args resultSort' scrutineeVal
  where
    instantiateRecursiveHeadArgs currentHeadArgs ctorHeadArgs =
      mapM sourceArg
      where
        sourceArg source =
          case source of
            RHOuterHeadArg i ->
              case nth currentHeadArgs i of
                Just arg -> Right arg
                Nothing -> Left "defeq: builtin eliminator recursive call is missing an outer head argument"
            RHCtorArg i ->
              case nth ctorHeadArgs i of
                Just arg -> Right arg
                Nothing -> Left "defeq: builtin eliminator recursive call is missing a constructor head argument"

evalBuiltinBinderBody
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Int]
  -> [Obj]
  -> [Val]
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text BTm
evalBuiltinBinderBody fragment tt convEnv outerBoundaryVars outerSortsOldToNew localTmCtxVals binderDomOldToNew codTy bodyDiag = do
  let binderCount = length binderDomOldToNew
      binderBoundaryVars = reverse [0 :: Int .. binderCount - 1]
      bodyAvailable = binderBoundaryVars <> map (+ binderCount) outerBoundaryVars
      expectedBoundarySorts = binderDomOldToNew <> outerSortsOldToNew
      bodyInCount = length (dIn bodyDiag)
      localTmCtxSorts = map valSort localTmCtxVals
  if bodyInCount >= binderCount && bodyInCount <= length bodyAvailable
    then Right ()
    else Left "defeq: builtin binder body must expose its bound variables first and then an outer-prefix"
  tmCtxMatch <- sortListsEq convEnv [] (dTmCtx bodyDiag) localTmCtxSorts
  if tmCtxMatch
    then Right ()
    else Left "defeq: builtin binder body term-context does not match the instantiated local term context"
  bodyInSorts <- mapM (requirePortSort bodyDiag "defeq: builtin binder body is missing a boundary input sort") (dIn bodyDiag)
  boundarySortsMatch <- sortListsEq convEnv [] bodyInSorts (take bodyInCount expectedBoundarySorts)
  if boundarySortsMatch
    then Right ()
    else Left "defeq: builtin binder body boundary sorts do not match the expected binder domain/prefix"
  let bodyBoundaryVars = take bodyInCount bodyAvailable
      outerEnvSize = binderCount + length outerSortsOldToNew
      ambientTmCtxVars =
        [ outerEnvSize + length localTmCtxVals - 1 - i
        | i <- [0 :: Int .. length localTmCtxVals - 1]
        ]
  diagramToBTmWithAmbient fragment tt convEnv bodyDiag bodyBoundaryVars ambientTmCtxVars (take bodyInCount expectedBoundarySorts) codTy (\_ _ _ _ -> Right Nothing)

instantiateBuiltinHeadSig
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> GenName
  -> [ValHeadArg]
  -> Either Text (TmHeadSig, M.Map TmVar CodeArg)
instantiateBuiltinHeadSig fragment tt convEnv tmCtx lvl resultSort g headArgs = do
  sig0 <-
    case lookupTmHeadSig tt (objOwnerMode resultSort) g of
      Just sig -> Right sig
      Nothing -> Left "defeq: builtin head is missing a term-head signature"
  if length headArgs == length (thsParams sig0)
    then Right ()
    else Left "defeq: builtin head parameter arity mismatch"
  let used = S.unions (map freeVarsObj (resultSort : tmCtx))
  let (sig, _, _) = freshenTmHeadSigAgainstWithMaps used sig0
  subst <-
    foldM
      stepParam
      M.empty
      (zip (thsParams sig) headArgs)
  pure (sig, subst)
  where
    stepParam substAcc (param, arg) =
      case (param, arg) of
        (GP_Ty v, VHAObj obj) -> do
          obj' <- tcNormalizeSort convEnv tmCtx obj
          bindHeadSubst v (CAObj obj') substAcc
        (GP_Ty _, VHATm _) ->
          Left "defeq: builtin head expected an object-valued parameter argument"
        (GP_Tm v, VHATm val) -> do
          expectedArgSort0 <- applyHeadSubstObj tt convEnv tmCtx substAcc (tmvSort v)
          expectedArgSort <- tcNormalizeSort convEnv tmCtx expectedArgSort0
          sortOk <- tcSortEq convEnv tmCtx (valSort val) expectedArgSort
          if sortOk
            then Right ()
            else Left "defeq: builtin head term parameter sort mismatch"
          tmDiag <- valueToTermDiagram fragment tt convEnv tmCtx lvl expectedArgSort val
          bindHeadSubst v (CATm tmDiag) substAcc
        (GP_Tm _, VHAObj _) ->
          Left "defeq: builtin head expected a term-valued parameter argument"

bindBuiltinHeadArgs
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> TmHeadSig
  -> [ValHeadArg]
  -> Either Text (M.Map TmVar CodeArg)
bindBuiltinHeadArgs fragment tt convEnv tmCtx lvl sig headArgs = do
  if length headArgs == length (thsParams sig)
    then Right ()
    else Left "defeq: builtin head parameter arity mismatch"
  foldM
    stepParam
    M.empty
    (zip (thsParams sig) headArgs)
  where
    stepParam substAcc (param, arg) =
      case (param, arg) of
        (GP_Ty v, VHAObj obj) -> do
          obj' <- tcNormalizeSort convEnv tmCtx obj
          bindHeadSubst v (CAObj obj') substAcc
        (GP_Ty _, VHATm _) ->
          Left "defeq: builtin head expected an object-valued parameter argument"
        (GP_Tm v, VHATm val) -> do
          expectedArgSort0 <- applyHeadSubstObj tt convEnv tmCtx substAcc (tmvSort v)
          expectedArgSort <- tcNormalizeSort convEnv tmCtx expectedArgSort0
          sortOk <- tcSortEq convEnv tmCtx (valSort val) expectedArgSort
          if sortOk
            then Right ()
            else Left "defeq: builtin head term parameter sort mismatch"
          tmDiag <- valueToTermDiagram fragment tt convEnv tmCtx lvl expectedArgSort val
          bindHeadSubst v (CATm tmDiag) substAcc
        (GP_Tm _, VHAObj _) ->
          Left "defeq: builtin head expected a term-valued parameter argument"

instantiateBuiltinResultSort
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> M.Map TmVar CodeArg
  -> TmHeadSig
  -> Either Text Obj
instantiateBuiltinResultSort tt convEnv tmCtx headSubst sig = do
  resultSort0 <- applyHeadSubstObj tt convEnv tmCtx headSubst (thsRes sig)
  tcNormalizeSort convEnv tmCtx resultSort0

prepareBuiltinBinderClosure
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> BinderSig
  -> ValBinderArg
  -> Either Text BinderClosure
prepareBuiltinBinderClosure _fragment _tt _convEnv tmCtx lvl slot barg = do
  bodyDiag <-
    case barg of
      VBABody body -> Right body
      VBAHole _ -> Left "defeq: builtin eliminator binder arguments must be concrete bodies"
  let ownerMode =
        case bsCod slot of
          (codTy:_) -> objOwnerMode codTy
          [] ->
            case bsDom slot of
              (domTy:_) -> objOwnerMode domTy
              [] ->
                case bsTmCtx slot of
                  (ctxTy:_) -> objOwnerMode ctxTy
                  [] -> dMode bodyDiag
  let modeInputsAll = modeCtx tmCtx ownerMode
  if lvl <= length modeInputsAll
    then Right ()
    else Left "defeq: builtin eliminator binder body requires larger mode-local context prefix than available"
  let outerSortsOldToNew = map snd (take lvl modeInputsAll)
  outerEnv <- mkInitialEnv lvl outerSortsOldToNew
  pure
    BinderClosure
      { bcRawBody = bodyDiag
      , bcSlotTemplate = slot
      , bcOuterSortsOldToNew = outerSortsOldToNew
      , bcOuterEnv = outerEnv
      }

resolveBuiltinLocalTmCtx
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> BinderClosure
  -> [Obj]
  -> [Val]
  -> Either Text ([Obj], M.Map Int TermDiagram)
resolveBuiltinLocalTmCtx fragment tt convEnv tmCtx closure slotTmCtx localTmCtxVals =
  go 0 [] M.empty slotTmCtx localTmCtxVals
  where
    lvl = length (bcOuterEnv closure)

    go _ acc subst [] [] =
      pure (reverse acc, subst)
    go i acc subst (expected0 : expectedRest) (val : valRest) = do
      expected1 <- instantiateHostBoundObj tt convEnv tmCtx subst expected0
      expected <- tcNormalizeSort convEnv tmCtx expected1
      ok <- tcSortEq convEnv tmCtx (valSort val) expected
      if ok
        then Right ()
        else Left "defeq: builtin eliminator binder local term-context sorts do not match the slot"
      tmDiag <- valueToTermDiagram fragment tt convEnv tmCtx lvl expected val
      go (i + 1) (expected : acc) (M.insert i tmDiag subst) expectedRest valRest
    go _ _ _ _ _ =
      Left "defeq: builtin eliminator binder local term-context arity mismatch"

materializeBuiltinBinderClosure
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> M.Map TmVar CodeArg
  -> BinderClosure
  -> [Val]
  -> Either Text (BinderSig, BTm)
materializeBuiltinBinderClosure fragment tt convEnv tmCtx headSubst closure localTmCtxVals = do
  slot0 <- instantiateRuleBinderSig tt convEnv tmCtx headSubst (bcSlotTemplate closure)
  (slotTmCtx, localTmSubst) <-
    resolveBuiltinLocalTmCtx fragment tt convEnv tmCtx closure (bsTmCtx slot0) localTmCtxVals
  dom0 <- mapM (instantiateHostBoundObj tt convEnv tmCtx localTmSubst) (bsDom slot0)
  dom' <- normalizeCtxStructurallyWithPrefix tt convEnv slotTmCtx dom0
  cod0 <- mapM (instantiateHostBoundObj tt convEnv tmCtx localTmSubst) (bsCod slot0)
  cod' <- normalizeCtxStructurallyWithPrefix tt convEnv slotTmCtx cod0
  let slot =
        slot0
          { bsTmCtx = slotTmCtx
          , bsDom = dom'
          , bsCod = cod'
          }
  codTy <-
    case bsCod slot of
      [codTy] -> Right codTy
      _ -> Left "defeq: builtin eliminator binder arguments must return exactly one term"
  let outerSortsOldToNew = bcOuterSortsOldToNew closure
      outerBoundaryVars = [length outerSortsOldToNew - 1, length outerSortsOldToNew - 2 .. 0]
  body <- evalBuiltinBinderBody fragment tt convEnv outerBoundaryVars outerSortsOldToNew localTmCtxVals (bsDom slot) codTy (bcRawBody closure)
  pure (slot, body)

applyBinderClosure
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> M.Map TmVar CodeArg
  -> BinderClosure
  -> [Val]
  -> [Val]
  -> Either Text Val
applyBinderClosure fragment tt convEnv tmCtx headSubst closure localTmCtxVals argsOldToNew = do
  (slot, body) <- materializeBuiltinBinderClosure fragment tt convEnv tmCtx headSubst closure localTmCtxVals
  if length argsOldToNew == length (bsDom slot)
    then Right ()
    else Left "defeq: builtin binder closure arity mismatch"
  argsMatch <- sortListsEq convEnv tmCtx (map valSort argsOldToNew) (bsDom slot)
  if argsMatch
    then Right ()
    else Left "defeq: builtin binder closure argument sorts do not match the binder domain"
  result <- evalBTm fragment tt convEnv tmCtx (reverse argsOldToNew <> bcOuterEnv closure <> reverse localTmCtxVals) body
  let codTy =
        case bsCod slot of
          [one] -> one
          _ -> error "unreachable: builtin binder closure codomain already checked"
  ok <- tcSortEq convEnv tmCtx (valSort result) codTy
  if ok
    then Right result
    else Left "defeq: builtin binder closure produced the wrong result sort"

headFrameArgs :: Int -> [Val] -> [ElimArg]
headFrameArgs holeIx vals =
  [ if i == holeIx then ElimHole else ElimVal val
  | (i, val) <- zip [0 :: Int ..] vals
  ]

sortListsEq :: TermConvEnv -> [Obj] -> [Obj] -> [Obj] -> Either Text Bool
sortListsEq convEnv tmCtx actual expected
  | length actual /= length expected =
      pure False
  | otherwise =
      foldM
        (\ok (a, b) -> if ok then tcSortEq convEnv tmCtx a b else pure False)
        True
        (zip actual expected)

replaceAt :: Int -> a -> [a] -> [a]
replaceAt needle x =
  zipWith (\i old -> if i == needle then x else old) [0 :: Int ..]

decodeBuiltinLamBody
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Int]
  -> [Obj]
  -> Obj
  -> Obj
  -> Obj
  -> Diagram
  -> Either Text BTm
decodeBuiltinLamBody fragment tt convEnv outerBoundaryVars outerSortsOldToNew _lamSort domTy codTy bodyDiag =
  evalBuiltinBinderBody fragment tt convEnv outerBoundaryVars outerSortsOldToNew [] [domTy] codTy bodyDiag

tryRewriteHead
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Val
  -> Either Text Val
tryRewriteHead fragment tt convEnv tmCtx lvl residual =
  case valExpr residual of
    VNeu neu ->
      case neu of
        NGen g _ _ _ -> tryRulesFor g
        NBind g _ _ _ _ -> tryRulesFor g
        _ -> Right residual
    _ ->
      Right residual
  where
    trs = dfCompiledRules fragment

    tryRulesFor g =
      tryRules
        ( M.findWithDefault [] (Just g) (RS.trsIndex trs)
            <> M.findWithDefault [] Nothing (RS.trsIndex trs)
        )

    tryRules [] = Right residual
    tryRules (rule:rest) = do
      matched <- matchRuleValue fragment tt convEnv tmCtx lvl emptyRuleSubst (RS.trLHS rule) residual
      case matched of
        Nothing -> tryRules rest
        Just subst ->
          case RS.trRHS rule of
            Just rhs ->
              evalRuleExpr fragment tt convEnv tmCtx lvl (valSort residual) subst rhs
            Nothing ->
              case RS.trRHSDiagram rule of
                Just rhsDiag ->
                  evalRuleDiagramRHS fragment tt convEnv tmCtx lvl (valSort residual) rule subst (unTerm rhsDiag)
                Nothing ->
                  Left "defeq: trusted rewrite rule is missing both term and diagram RHS forms"

matchRuleValue
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> RuleSubst
  -> TermExpr
  -> Val
  -> Either Text (Maybe RuleSubst)
matchRuleValue fragment tt convEnv tmCtx lvl subst pat val =
  case pat of
    TMBound i ->
      bindRuleVar fragment tt convEnv tmCtx lvl i val subst
    TMMeta v args ->
      case valExpr val of
        VNeu (NMeta w argVals)
          | v == w
          , length args == length argVals ->
              foldM
                step
                (Just subst)
                (zip args argVals)
          | otherwise ->
              pure Nothing
        _ ->
          pure Nothing
      where
        step Nothing _ = pure Nothing
        step (Just substAcc) (i, argVal) =
          bindRuleVar fragment tt convEnv tmCtx lvl i argVal substAcc
    TMLit lit ->
      case valExpr val of
        VLit lit'
          | lit == lit' -> pure (Just subst)
          | otherwise -> pure Nothing
        _ -> pure Nothing
    TMSplice _ _ _ ->
      pure Nothing
    TMHead f flatArgs bargs ->
      case headView fragment val of
        Just (g, targetHeadArgs, targetInputs, targetBinders)
          | f == g -> do
              sig <-
                case lookupTmHeadSig tt (objOwnerMode (valSort val)) f of
                  Just sig0 -> Right sig0
                  Nothing -> Left "defeq: unknown head while matching trusted rewrite rule"
              if length flatArgs == length (thsParams sig) + length (thsInputs sig)
                  && length bargs == length (thsBinders sig)
                then do
                  let (paramPats, inputPats) = splitAt (length (thsParams sig)) flatArgs
                  matchedParams <-
                    foldM
                      matchParam
                      (Just subst)
                      (zip paramPats targetHeadArgs)
                  foldM
                    matchInput
                    matchedParams
                    (zip inputPats targetInputs)
                    >>= \matchedInputs ->
                      foldM
                        matchBinder
                        matchedInputs
                        (zip3 (thsBinders sig) bargs targetBinders)
                else pure Nothing
          | otherwise ->
              pure Nothing
        _ ->
          pure Nothing
  where
    matchParam Nothing _ = pure Nothing
    matchParam (Just substAcc) (paramPat, targetArg) =
      case (paramPat, targetArg) of
        (THAObj patObj, VHAObj targetObj) ->
          matchRuleObj tt convEnv tmCtx substAcc patObj targetObj
        (THATm patTm, VHATm targetVal) ->
          matchRuleValue fragment tt convEnv tmCtx lvl substAcc patTm targetVal
        _ ->
          pure Nothing

    matchInput Nothing _ = pure Nothing
    matchInput (Just substAcc) (inputPat, targetVal) =
      case inputPat of
        THATm patTm ->
          matchRuleValue fragment tt convEnv tmCtx lvl substAcc patTm targetVal
        THAObj _ ->
          pure Nothing

    matchBinder Nothing _ = pure Nothing
    matchBinder (Just substAcc) (slot0, TBABody patDiag, VBABody targetDiag) = do
      slot <- instantiateRuleBinderSig tt convEnv tmCtx (rsHeadSubst substAcc) slot0
      patDiag' <- canonicalizeRuleBinderDiagram tt convEnv (rsHeadSubst substAcc) patDiag
      targetDiag' <- canonicalizeRuleBinderDiagram tt convEnv M.empty targetDiag
      validateRuleBinderDiagram slot targetDiag'
      pure
        ( if patDiag' == targetDiag'
            then Just substAcc
            else Nothing
        )
    matchBinder (Just _substAcc) (_slot0, TBABody _patDiag, VBAHole _) =
      pure Nothing
    matchBinder (Just substAcc) (slot0, TBAHole hole, VBABody targetDiag) = do
      slot <- instantiateRuleBinderSig tt convEnv tmCtx (rsHeadSubst substAcc) slot0
      targetDiag' <- canonicalizeRuleBinderDiagram tt convEnv M.empty targetDiag
      validateRuleBinderDiagram slot targetDiag'
      case M.lookup hole (rsBinderVals substAcc) of
        Nothing ->
          pure
            ( Just
                substAcc
                  { rsBinderVals =
                      M.insert
                        hole
                        RuleBinderCapture
                          { rbcSlot =
                              slot
                          , rbcValue = RBCConcrete targetDiag'
                          }
                        (rsBinderVals substAcc)
                  }
            )
        Just capture -> do
          pure
            ( if rbcSlot capture == slot
                  && rbcValue capture == RBCConcrete targetDiag'
                then Just substAcc
                else Nothing
            )
    matchBinder (Just substAcc) (slot0, TBAHole hole, VBAHole hole')
      | hole == hole' =
          do
            slot <- instantiateRuleBinderSig tt convEnv tmCtx (rsHeadSubst substAcc) slot0
            case M.lookup hole (rsBinderVals substAcc) of
              Nothing ->
                pure
                  ( Just
                      substAcc
                        { rsBinderVals =
                            M.insert
                              hole
                              RuleBinderCapture
                                { rbcSlot = slot
                                , rbcValue = RBCSymbolic hole'
                                }
                              (rsBinderVals substAcc)
                        }
                  )
              Just capture ->
                pure
                  ( if rbcSlot capture == slot
                        && rbcValue capture == RBCSymbolic hole'
                      then Just substAcc
                      else Nothing
                  )
      | otherwise =
          pure Nothing

bindRuleVar
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Int
  -> Val
  -> RuleSubst
  -> Either Text (Maybe RuleSubst)
bindRuleVar fragment tt convEnv tmCtx lvl i val subst =
  case M.lookup i (rsBoundVals subst) of
    Nothing ->
      pure
        ( Just
            subst
              { rsBoundVals = M.insert i val (rsBoundVals subst)
              }
        )
    Just old -> do
      same <- valuesEqual fragment tt convEnv tmCtx lvl old val
      pure
        ( if same
            then Just subst
            else Nothing
        )

bindRuleObjMeta
  :: TermConvEnv
  -> [Obj]
  -> TmVar
  -> Obj
  -> RuleSubst
  -> Either Text (Maybe RuleSubst)
bindRuleObjMeta convEnv tmCtx v obj subst =
  case M.lookup v (rsHeadSubst subst) of
    Nothing ->
      pure
        ( Just
            subst
              { rsHeadSubst = M.insert v (CAObj obj) (rsHeadSubst subst)
              }
        )
    Just (CAObj old) -> do
      old' <- tcNormalizeSort convEnv tmCtx old
      obj' <- tcNormalizeSort convEnv tmCtx obj
      same <- tcSortEq convEnv tmCtx old' obj'
      pure
        ( if same
            then Just subst
            else Nothing
        )
    Just (CATm _) ->
      pure Nothing

instantiateRuleObj
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> RuleSubst
  -> Obj
  -> Either Text Obj
instantiateRuleObj tt convEnv tmCtx subst obj = do
  obj' <- applyHeadSubstObj tt convEnv tmCtx (rsHeadSubst subst) obj
  tcNormalizeSort convEnv tmCtx obj'

matchRuleObj
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> RuleSubst
  -> Obj
  -> Obj
  -> Either Text (Maybe RuleSubst)
matchRuleObj tt convEnv tmCtx subst patObj targetObj = do
  patObj' <- instantiateRuleObj tt convEnv tmCtx subst patObj
  targetObj' <- tcNormalizeSort convEnv tmCtx targetObj
  go subst patObj' targetObj'
  where
    go substAcc pat target
      | pat == target =
          pure (Just substAcc)
      | objOwnerMode pat /= objOwnerMode target =
          pure Nothing
      | otherwise =
          case (objCode pat, objCode target) of
            (CTMeta v, _) ->
              bindRuleObjMeta convEnv tmCtx v target substAcc
            (CTCon refA argsA, CTCon refB argsB)
              | refA == refB
              , length argsA == length argsB ->
                  foldM
                    step
                    (Just substAcc)
                    (zip argsA argsB)
              | otherwise ->
                  pure Nothing
            (CTLift meA _, CTLift meB _)
              | meA == meB ->
                  pure
                    ( if pat == target
                        then Just substAcc
                        else Nothing
                    )
              | otherwise ->
                  pure Nothing
            _ ->
              pure Nothing

    step Nothing _ = pure Nothing
    step (Just substAcc) (argA, argB) =
      case (argA, argB) of
        (CAObj objA, CAObj objB) ->
          matchRuleObj tt convEnv tmCtx substAcc objA objB
        (CATm tmA, CATm tmB) ->
          pure
            ( if tmA == tmB
                then Just substAcc
                else Nothing
            )
        _ ->
          pure Nothing

valuesEqual
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Val
  -> Val
  -> Either Text Bool
valuesEqual fragment tt convEnv tmCtx lvl a b = do
  sortsAgree <- tcSortEq convEnv tmCtx (valSort a) (valSort b)
  if not sortsAgree
    then pure False
    else do
      sharedSort <- tcNormalizeSort convEnv tmCtx (valSort a)
      a' <- quoteValAtSort fragment tt convEnv tmCtx lvl sharedSort a
      b' <- quoteValAtSort fragment tt convEnv tmCtx lvl sharedSort b
      pure (a' == b')

headView :: DefFragment -> Val -> Maybe (GenName, [ValHeadArg], [Val], [ValBinderArg])
headView fragment val =
  case valExpr val of
    VNeu (NGen g headArgs args _) ->
      Just (g, headArgs, args, [])
    VNeu (NBind g headArgs args binderArgs _) ->
      Just (g, headArgs, args, binderArgs)
    VNeu (NElim fun (AppFrame headArgs arg _domTy _codTy)) -> do
      fb <- functionBuiltin fragment
      let funVal = neutralValue fun
      Just (fbAppGen fb, headArgs, [funVal, arg], [])
    _ ->
      Nothing

evalRuleDiagramRHS
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> RS.TRule
  -> RuleSubst
  -> Diagram
  -> Either Text Val
evalRuleDiagramRHS fragment tt convEnv tmCtx _lvl expectedSort rule subst rhsDiag0 = do
  rhsDiag <- instantiateRuleDiagramRHS tt convEnv subst rhsDiag0
  let nIn = length (dIn rhsDiag)
  if nIn == length (RS.trVars rule)
    then Right ()
    else Left "defeq: trusted rewrite diagram RHS boundary arity does not match rule variable context"
  expectedSort' <- tcNormalizeSort convEnv tmCtx expectedSort
  btm <-
    diagramToBTmWith
      fragment
      tt
      convEnv
      rhsDiag
      [nIn - 1, nIn - 2 .. 0]
      []
      (map tmvSort (RS.trVars rule))
      expectedSort'
      (resolveRuleVarMeta rhsDiag nIn)
  env <- mapM lookupRuleVal [0 .. nIn - 1]
  evalBTm fragment tt convEnv tmCtx (reverse env) btm
  where
    lookupRuleVal i =
      case M.lookup i (rsBoundVals subst) of
        Just val -> Right val
        Nothing -> Left "defeq: missing trusted rewrite variable during diagram RHS evaluation"

    resolveRuleVarMeta rhsDiag nIn boundarySorts currentSort v ins =
      case findRuleVarIndex v (RS.trVars rule) 0 of
        Nothing -> Right Nothing
        Just i -> do
          actualArgs <- mapM boundaryLocalIndex ins
          let expectedArgs = defaultMetaArgs boundarySorts v
          if actualArgs == expectedArgs
            then do
              sortTy <- tcNormalizeSort convEnv boundarySorts (tmvSort v)
              sortMatches <- tcSortEq convEnv boundarySorts sortTy currentSort
              if sortMatches
                then
                  case nth [nIn - 1, nIn - 2 .. 0] i of
                    Just bvarIx ->
                      pure (Just BTm { btSort = sortTy, btExpr = BVar bvarIx })
                    Nothing ->
                      Left "defeq: trusted rewrite diagram RHS variable index out of range"
                else Left "defeq: trusted rewrite diagram RHS variable sort mismatch"
            else
              Left "defeq: trusted rewrite diagram RHS uses a rule variable with non-canonical arguments"
      where
        boundaryLocalIndex pid =
          case M.lookup pid (M.fromList (zip (dIn rhsDiag) [0 :: Int ..])) of
            Just localIx -> Right localIx
            Nothing -> Left "defeq: trusted rewrite diagram RHS metavariable inputs must connect to boundary ports"

findRuleVarIndex :: TmVar -> [TmVar] -> Int -> Maybe Int
findRuleVarIndex _ [] _ = Nothing
findRuleVarIndex v (x:xs) i
  | sameTmVarId v x = Just i
  | otherwise = findRuleVarIndex v xs (i + 1)

instantiateRuleDiagramRHS
  :: TypeTheory
  -> TermConvEnv
  -> RuleSubst
  -> Diagram
  -> Either Text Diagram
instantiateRuleDiagramRHS tt convEnv subst rhsDiag0 = do
  headSubst <- mkSubst (M.toList (rsHeadSubst subst))
  rhsDiag1 <- applySubstDiagramWith (termSubstOps tt convEnv) tt headSubst rhsDiag0
  rhsDiag2 <- traverseDiagram pure rewriteSpliceRef pure rewriteBinderArg rhsDiag1
  rhsDiag3 <- expandSplices (tcSpliceMapper convEnv) concreteBinderSub rhsDiag2
  canonDiagramRaw rhsDiag3
  where
    concreteBinderSub =
      M.mapMaybe concreteBinderBody (rsBinderVals subst)

    concreteBinderBody capture =
      case rbcValue capture of
        RBCConcrete body -> Just body
        RBCSymbolic _ -> Nothing

    rewriteSpliceRef payload =
      case payload of
        PSplice hole me ->
          case M.lookup hole (rsBinderVals subst) of
            Just capture ->
              case rbcValue capture of
                RBCConcrete _ -> Right payload
                RBCSymbolic hole' -> Right (PSplice hole' me)
            Nothing -> Left "defeq: trusted rewrite diagram RHS uses uncaptured binder meta"
        _ -> Right payload

    rewriteBinderArg barg =
      case barg of
        BAConcrete inner -> Right (BAConcrete inner)
        BAMeta hole ->
          case M.lookup hole (rsBinderVals subst) of
            Nothing -> Left "defeq: trusted rewrite diagram RHS uses uncaptured binder meta"
            Just capture ->
              case rbcValue capture of
                RBCConcrete body -> Right (BAConcrete body)
                RBCSymbolic hole' -> Right (BAMeta hole')

evalRuleExpr
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> RuleSubst
  -> TermExpr
  -> Either Text Val
evalRuleExpr fragment tt convEnv tmCtx lvl expectedSort subst expr =
  case expr of
    TMBound i ->
      case M.lookup i (rsBoundVals subst) of
        Nothing ->
          Left "defeq: missing trusted rewrite variable during RHS instantiation"
        Just val -> do
          ok <- tcSortEq convEnv tmCtx (valSort val) expectedSort
          if ok
            then Right val
            else Left "defeq: trusted rewrite variable sort mismatch during RHS instantiation"
    TMMeta v args -> do
      argVals <- mapM lookupBound args
      pure
        Val
          { valSort = expectedSort
          , valExpr = VNeu (NMeta v argVals)
          }
    TMLit lit ->
      pure
        Val
          { valSort = expectedSort
          , valExpr = VLit lit
          }
    TMSplice hole me args ->
      evalRuleSplice fragment tt convEnv tmCtx lvl expectedSort subst hole me args
    TMHead f flatArgs bargs -> do
      currentSort <- tcNormalizeSort convEnv tmCtx expectedSort
      sig0 <-
        case lookupTmHeadSig tt (objOwnerMode currentSort) f of
          Just sig -> Right sig
          Nothing -> Left "defeq: unknown head while evaluating trusted rewrite RHS"
      let used = S.unions (map freeVarsObj (currentSort : tmCtx))
      let (sig, _, _) = freshenTmHeadSigAgainstWithMaps used sig0
      if length flatArgs /= length (thsParams sig) + length (thsInputs sig)
          || length bargs /= length (thsBinders sig)
        then Left "defeq: trusted rewrite RHS head arity mismatch"
        else do
          let (paramArgs, inputArgs) = splitAt (length (thsParams sig)) flatArgs
          (headValsRev, headSubst) <-
            foldM
              stepParam
              ([], M.empty)
              (zip (thsParams sig) paramArgs)
          inputValsRev <-
            foldM
              (stepInput headSubst)
              []
              (zip (thsInputs sig) inputArgs)
          binderValsRev <-
            foldM
              (stepBinder headSubst)
              []
              (zip (thsBinders sig) bargs)
          resSort0 <- applyHeadSubstObj tt convEnv tmCtx headSubst (thsRes sig)
          resSort <- tcNormalizeSort convEnv tmCtx resSort0
          ok <- tcSortEq convEnv tmCtx resSort currentSort
          if ok
            then
              if null binderValsRev
                then
                  evalHeadApplication
                    fragment
                    tt
                    convEnv
                    tmCtx
                    lvl
                    currentSort
                    f
                    (reverse headValsRev)
                    (reverse inputValsRev)
                else
                  evalBinderHeadApplication
                    fragment
                    tt
                    convEnv
                    tmCtx
                    lvl
                    currentSort
                    f
                    (reverse headValsRev)
                    (reverse inputValsRev)
                    (reverse binderValsRev)
            else Left "defeq: trusted rewrite RHS head result sort mismatch"
  where
    lookupBound i =
      case M.lookup i (rsBoundVals subst) of
        Just val -> Right val
        Nothing -> Left "defeq: missing trusted rewrite variable in metavariable spine"

    stepParam (headValsAcc, headSubstAcc) (param, arg) =
      case (param, arg) of
        (GP_Ty v, THAObj obj) -> do
          obj' <- instantiateRuleObj tt convEnv tmCtx subst obj
          headSubst' <- bindHeadSubst v (CAObj obj') headSubstAcc
          pure (VHAObj obj' : headValsAcc, headSubst')
        (GP_Ty _, THATm _) ->
          Left "defeq: trusted rewrite RHS expected object-valued parameter argument"
        (GP_Tm v, THATm tmArg) -> do
          expectedArgSort0 <- applyHeadSubstObj tt convEnv tmCtx headSubstAcc (tmvSort v)
          expectedArgSort <- tcNormalizeSort convEnv tmCtx expectedArgSort0
          val <- evalRuleExpr fragment tt convEnv tmCtx lvl expectedArgSort subst tmArg
          tmDiag <- valueToTermDiagram fragment tt convEnv tmCtx lvl expectedArgSort val
          headSubst' <- bindHeadSubst v (CATm tmDiag) headSubstAcc
          pure (VHATm val : headValsAcc, headSubst')
        (GP_Tm _, THAObj _) ->
          Left "defeq: trusted rewrite RHS expected term-valued parameter argument"

    stepInput headSubstAcc inputValsAcc (argSort, arg) =
      case arg of
        THATm tmArg -> do
          expectedArgSort0 <- applyHeadSubstObj tt convEnv tmCtx headSubstAcc argSort
          expectedArgSort <- tcNormalizeSort convEnv tmCtx expectedArgSort0
          val <- evalRuleExpr fragment tt convEnv tmCtx lvl expectedArgSort subst tmArg
          pure (val : inputValsAcc)
        THAObj _ ->
          Left "defeq: trusted rewrite RHS expected term input argument"

    stepBinder headSubstAcc binderValsAcc (slot0, barg) = do
      slot <- instantiateRuleBinderSig tt convEnv tmCtx headSubstAcc slot0
      barg' <- instantiateRuleBinderArg tt convEnv headSubstAcc subst slot barg
      pure (barg' : binderValsAcc)

instantiateRuleBinderSig
  :: TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> M.Map TmVar CodeArg
  -> BinderSig
  -> Either Text BinderSig
instantiateRuleBinderSig tt convEnv tmCtx headSubst slot = do
  tmCtx0 <- mapM (applyHeadSubstObj tt convEnv tmCtx headSubst) (bsTmCtx slot)
  tmCtx' <- normalizeCtxStructurally tt convEnv tmCtx0
  dom0 <- mapM (applyHeadSubstObj tt convEnv tmCtx' headSubst) (bsDom slot)
  dom' <- normalizeCtxStructurallyWithPrefix tt convEnv tmCtx' dom0
  cod0 <- mapM (applyHeadSubstObj tt convEnv tmCtx' headSubst) (bsCod slot)
  cod' <- normalizeCtxStructurallyWithPrefix tt convEnv tmCtx' cod0
  pure slot { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }

instantiateRuleBinderArg
  :: TypeTheory
  -> TermConvEnv
  -> M.Map TmVar CodeArg
  -> RuleSubst
  -> BinderSig
  -> TermBinderArg
  -> Either Text ValBinderArg
instantiateRuleBinderArg tt convEnv headSubst subst slot barg =
  case barg of
    TBABody inner0 -> do
      inner <- canonicalizeRuleBinderDiagram tt convEnv headSubst inner0
      validateRuleBinderDiagram slot inner
      pure (VBABody inner)
    TBAHole hole ->
      case M.lookup hole (rsBinderVals subst) of
        Nothing ->
          Left "defeq: missing trusted rewrite binder-hole capture during RHS instantiation"
        Just capture -> do
          if rbcSlot capture == slot
            then
              case rbcValue capture of
                RBCConcrete body -> do
                  validateRuleBinderDiagram slot body
                  pure (VBABody body)
                RBCSymbolic hole' ->
                  pure (VBAHole hole')
            else Left "defeq: binder-hole capture slot mismatch during RHS instantiation"

evalRuleSplice
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> RuleSubst
  -> BinderMetaVar
  -> ModExpr
  -> [TermExpr]
  -> Either Text Val
evalRuleSplice fragment tt convEnv tmCtx lvl expectedSort subst hole me args = do
  capture <-
    case M.lookup hole (rsBinderVals subst) of
      Nothing ->
        Left "defeq: missing trusted rewrite binder-hole capture during splice evaluation"
      Just one ->
        Right one
  case rbcValue capture of
    RBCConcrete captured0 -> do
      captured <- tcSpliceMapper convEnv me captured0
      let inputPids = dIn captured
      if length args == length inputPids
        then Right ()
        else Left "defeq: trusted rewrite splice arity mismatch"
      inputSorts <- diagramBoundaryTypes captured inputPids
      argVals <-
        mapM
          (\(argSort, arg) -> evalRuleExpr fragment tt convEnv tmCtx lvl argSort subst arg)
          (zip inputSorts args)
      expectedSort' <- tcNormalizeSort convEnv tmCtx expectedSort
      btm <-
        diagramToBTm
          fragment
          tt
          convEnv
          captured
          [length inputSorts - 1, length inputSorts - 2 .. 0]
          inputSorts
          expectedSort'
      evalBTm fragment tt convEnv (dTmCtx captured) (reverse argVals) btm
    RBCSymbolic hole' -> do
      let inputSorts = bsDom (rbcSlot capture)
      if length args == length inputSorts
        then Right ()
        else Left "defeq: trusted rewrite splice arity mismatch"
      argVals <-
        mapM
          (\(argSort, arg) -> evalRuleExpr fragment tt convEnv tmCtx lvl argSort subst arg)
          (zip inputSorts args)
      expectedSort' <- tcNormalizeSort convEnv tmCtx expectedSort
      pure
        Val
          { valSort = expectedSort'
          , valExpr = VNeu (NSplice hole' me argVals expectedSort')
          }

canonicalizeRuleBinderDiagram
  :: TypeTheory
  -> TermConvEnv
  -> M.Map TmVar CodeArg
  -> Diagram
  -> Either Text Diagram
canonicalizeRuleBinderDiagram tt convEnv headSubst inner = do
  subst <- mkSubst (M.toList headSubst)
  inner' <- applySubstDiagramWith (termSubstOps tt convEnv) tt subst inner
  canonDiagramRaw inner'

validateRuleBinderDiagram :: BinderSig -> Diagram -> Either Text ()
validateRuleBinderDiagram slot inner = do
  validateDiagram inner
  if dTmCtx inner == bsTmCtx slot
    then Right ()
    else Left "defeq: trusted rewrite binder argument term-context mismatch"
  dom <- diagramBoundaryTypes inner (dIn inner)
  cod <- diagramBoundaryTypes inner (dOut inner)
  if dom == bsDom slot && cod == bsCod slot
    then Right ()
    else Left "defeq: trusted rewrite binder argument boundary mismatch"

diagramBoundaryTypes :: Diagram -> [PortId] -> Either Text [Obj]
diagramBoundaryTypes diag =
  mapM
    ( \pid ->
        case diagramPortObj diag pid of
          Just ty -> Right ty
          Nothing -> Left "defeq: trusted rewrite binder argument is missing a boundary sort"
    )

applyVal :: DefFragment -> TermConvEnv -> [Obj] -> Maybe [ValHeadArg] -> Val -> Val -> Either Text Val
applyVal fragment convEnv tmCtx mHeadArgs funVal argVal =
  case valExpr funVal of
    VLam _ f -> f argVal
    VLit _ ->
      Left "NbE: attempted to apply a literal"
    VNeu n ->
      case splitArr fragment (valSort funVal) of
        Just (domTy, codTy) -> do
          domMatches <- tcSortEq convEnv tmCtx domTy (valSort argVal)
          if domMatches
            then
              let headArgs = maybe (synthAppHeadArgs domTy codTy) id mHeadArgs
               in Right
                    (neutralValue (NElim n (AppFrame headArgs argVal domTy codTy)))
            else Left "NbE: neutral application argument sort mismatch"
        Nothing ->
          Left "NbE: attempted to apply a non-function neutral"

reify :: DefFragment -> TypeTheory -> TermConvEnv -> [Obj] -> Int -> Obj -> Val -> Either Text BTm
reify fragment tt convEnv tmCtx lvl expectedSort val =
  case functionBuiltin fragment >>= \fb -> fmap (\parts -> (fb, parts)) (splitArr fragment expectedSort) of
    Just (fb, (domTy, codTy))
      | fbAllowEta fb -> do
          let fresh = neutralVar lvl domTy
          bodyVal <- applyVal fragment convEnv tmCtx Nothing val fresh
          body <- reify fragment tt convEnv tmCtx (lvl + 1) codTy bodyVal
          pure BTm { btSort = expectedSort, btExpr = BLam (synthArrHeadArgs fragment expectedSort) body }
    _ ->
      quoteValAtSort fragment tt convEnv tmCtx lvl expectedSort val

quoteValAtSort
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> Val
  -> Either Text BTm
quoteValAtSort fragment tt convEnv tmCtx lvl sortTy val =
  case valExpr val of
    VLit lit ->
      pure BTm { btSort = sortTy, btExpr = BLit lit }
    VNeu neu ->
      quoteNeuAtSort fragment tt convEnv tmCtx lvl sortTy neu
    VLam headArgs f ->
      case splitArr fragment sortTy of
        Just (domTy, codTy) -> do
          let fresh = neutralVar lvl domTy
          bodyVal <- f fresh
          body <- quoteValAtSort fragment tt convEnv tmCtx (lvl + 1) codTy bodyVal
          headArgs' <- mapM (quoteHeadArgAtSort fragment tt convEnv tmCtx lvl) headArgs
          pure BTm { btSort = sortTy, btExpr = BLam headArgs' body }
        Nothing ->
          Left "NbE: cannot quote lambda at non-function sort"

quoteHeadArgAtSort
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> ValHeadArg
  -> Either Text BTmHeadArg
quoteHeadArgAtSort fragment tt convEnv tmCtx lvl arg =
  case arg of
    VHAObj obj -> pure (BHAObj obj)
    VHATm val -> BHATm <$> quoteValAtSort fragment tt convEnv tmCtx lvl (valSort val) val

quoteNeu
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Neu
  -> Either Text BTm
quoteNeu fragment tt convEnv tmCtx lvl neu =
  quoteNeuAtSort fragment tt convEnv tmCtx lvl (neutralSort neu) neu

quoteNeuAtSort
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> Neu
  -> Either Text BTm
quoteNeuAtSort fragment tt convEnv tmCtx lvl sortTy neu =
  case neu of
    NVar level _ -> do
      let idx = lvl - level - 1
      if idx >= 0
        then pure BTm { btSort = sortTy, btExpr = BVar idx }
        else Left "NbE: internal level/index conversion underflow"
    NMeta v args -> do
      argIdx <- mapM (metaArgIndex lvl) args
      pure BTm { btSort = sortTy, btExpr = BMeta (v { tmvSort = sortTy }) argIdx }
    NGen g headArgs args _ -> do
      headArgs' <- mapM (quoteHeadArgAtSort fragment tt convEnv tmCtx lvl) headArgs
      args' <- mapM (\v -> quoteValAtSort fragment tt convEnv tmCtx lvl (valSort v) v) args
      pure BTm { btSort = sortTy, btExpr = BGen g headArgs' args' }
    NBind g headArgs args binderArgs _ -> do
      headArgs' <- mapM (quoteHeadArgAtSort fragment tt convEnv tmCtx lvl) headArgs
      args' <- mapM (\v -> quoteValAtSort fragment tt convEnv tmCtx lvl (valSort v) v) args
      pure
        BTm
          { btSort = sortTy
          , btExpr = BBind g headArgs' args' (map quoteBinderArg binderArgs)
          }
    NDiagram residual _ ->
      pure BTm { btSort = sortTy, btExpr = BResidual residual }
    NSplice hole me args _ -> do
      args' <- mapM (\v -> quoteValAtSort fragment tt convEnv tmCtx lvl (valSort v) v) args
      pure
        BTm
          { btSort = sortTy
          , btExpr = BSplice hole me args'
          }
    NElim base frame -> do
      baseTm <- quoteNeu fragment tt convEnv tmCtx lvl base
      quoteElimFrame fragment tt convEnv tmCtx lvl sortTy baseTm frame
  where
    quoteBinderArg barg =
      case barg of
        VBABody inner -> BBABody inner
        VBAHole hole -> BBAHole hole

quoteElimFrame
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> BTm
  -> ElimFrame
  -> Either Text BTm
quoteElimFrame fragment tt convEnv tmCtx lvl sortTy baseTm frame =
  case frame of
    AppFrame headArgs arg domTy _codTy -> do
      argTm <- quoteValAtSort fragment tt convEnv tmCtx lvl domTy arg
      headArgs' <- mapM (quoteHeadArgAtSort fragment tt convEnv tmCtx lvl) headArgs
      pure BTm { btSort = sortTy, btExpr = BApp headArgs' baseTm argTm }
    BuiltinElimFrame g headArgs args binderClosures _ -> do
      headArgs' <- mapM (quoteHeadArgAtSort fragment tt convEnv tmCtx lvl) headArgs
      args' <- mapM quoteElimArg args
      let binderArgs' = map (BBABody . bcRawBody) binderClosures
      pure
        BTm
          { btSort = sortTy
          , btExpr =
              if null binderArgs'
                then BGen g headArgs' args'
                else BBind g headArgs' args' binderArgs'
          }
  where
    quoteElimArg arg =
      case arg of
        ElimHole -> Right baseTm
        ElimVal val -> quoteValAtSort fragment tt convEnv tmCtx lvl (valSort val) val

btmToDiagram
  :: TypeTheory
  -> DefFragment
  -> [Obj]
  -> Obj
  -> [Obj]
  -> BTm
  -> Either Text Diagram
btmToDiagram tt fragment tmCtx expectedSort inSorts tm = do
  let mode = objOwnerMode expectedSort
  let modeInputsAll = modeCtx tmCtx mode
  let tmCtxPrefix =
        case take (length inSorts) modeInputsAll of
          [] -> []
          neededEntries ->
            let cutoff = maximum (map fst neededEntries)
             in take (cutoff + 1) tmCtx
  let (inPorts, d0) = allocPorts inSorts (emptyDiagram mode tmCtxPrefix)
  let varsNearest = reverse (zip inSorts inPorts)
  let ctx0 =
        BuildCtx
          { bcMode = mode
          , bcTmCtx = tmCtxPrefix
          , bcVarsNearest = varsNearest
          , bcBoundaryOldToNew = inPorts
          }
  (outPort, d1) <- buildBTm tt fragment ctx0 d0 tm
  finalizeSingleOutputDiagram inPorts outPort d1

data BuildCtx = BuildCtx
  { bcMode :: ModeName
  , bcTmCtx :: [Obj]
  , bcVarsNearest :: [(Obj, PortId)]
  , bcBoundaryOldToNew :: [PortId]
  }

buildBTm :: TypeTheory -> DefFragment -> BuildCtx -> Diagram -> BTm -> Either Text (PortId, Diagram)
buildBTm tt fragment ctx diag tm =
  case btExpr tm of
    BVar i ->
      case nth (bcVarsNearest ctx) i of
        Just (sortTy, pid)
          | sortTy == btSort tm -> Right (pid, diag)
          | otherwise -> Left "NbE: variable sort mismatch during diagram quoting"
        Nothing -> Left "NbE: de Bruijn variable out of scope during diagram quoting"
    BMeta v args -> do
      let v' = v { tmvSort = btSort tm }
      argPorts <- mapM (metaArgPort ctx) args
      emitMetaNode (btSort tm) v' argPorts diag
    BGen g headArgs args -> do
      storedArgs <- mapM buildHeadArgForCtx headArgs
      (argPorts, d0) <- foldM step ([], diag) args
      emitGenNode (btSort tm) g storedArgs [] argPorts d0
      where
        step (ports, dAcc) arg = do
          (pid, dNext) <- buildBTm tt fragment ctx dAcc arg
          pure (ports <> [pid], dNext)
    BBind g headArgs args binderArgs -> do
      storedArgs <- mapM buildHeadArgForCtx headArgs
      (argPorts, d0) <- foldM step ([], diag) args
      let bargs = map buildBinderArg binderArgs
      emitGenNode (btSort tm) g storedArgs bargs argPorts d0
      where
        step (ports, dAcc) arg = do
          (pid, dNext) <- buildBTm tt fragment ctx dAcc arg
          pure (ports <> [pid], dNext)
    BResidual residual ->
      embedResidualDiagram ctx diag (btSort tm) residual
    BSplice hole me args -> do
      (argPorts, d0) <- foldM step ([], diag) args
      emitSpliceNode (btSort tm) hole me argPorts d0
      where
        step (ports, dAcc) arg = do
          (pid, dNext) <- buildBTm tt fragment ctx dAcc arg
          pure (ports <> [pid], dNext)
    BLit lit -> do
      emitLiteralNode (btSort tm) lit diag
    BLam headArgs body -> do
      storedArgs <- mapM buildHeadArgForCtx headArgs
      (domTy, _codTy) <-
        case splitArr fragment (btSort tm) of
          Just parts -> Right parts
          Nothing -> Left "NbE: BLam node has non-function sort"
      let outerNearest = bcVarsNearest ctx
      let outerOldToNew = reverse outerNearest
      let innerInTys = domTy : map fst outerOldToNew
      let (innerInPorts, inner0) = allocPorts innerInTys (emptyDiagram (bcMode ctx) (bcTmCtx ctx))
      let boundPort =
            case innerInPorts of
              (p:_) -> p
              [] -> error "NbE internal: lambda inner boundary unexpectedly empty"
      let outerPortsOldToNew = drop 1 innerInPorts
      let outerPortsNearest = reverse outerPortsOldToNew
      let innerVarsNearest = (domTy, boundPort) : zip (map fst outerNearest) outerPortsNearest
      let innerCtx =
            BuildCtx
              { bcMode = bcMode ctx
              , bcTmCtx = bcTmCtx ctx
              , bcVarsNearest = innerVarsNearest
              , bcBoundaryOldToNew = innerInPorts
              }
      (innerOut, innerBuilt0) <- buildBTm tt fragment innerCtx inner0 body
      innerBuilt <- finalizeSingleOutputDiagram innerInPorts innerOut innerBuilt0
      validateDiagram innerBuilt
      case functionBuiltin fragment of
        Just fb ->
          emitGenNode (btSort tm) (fbLamGen fb) storedArgs [BAConcrete innerBuilt] [] diag
        Nothing ->
          Left "defeq: cannot quote lambda without function-space builtins"
    BApp headArgs f a -> do
      storedArgs <- mapM buildHeadArgForCtx headArgs
      (fPort, d0) <- buildBTm tt fragment ctx diag f
      (aPort, d1) <- buildBTm tt fragment ctx d0 a
      case functionBuiltin fragment of
        Just fb ->
          emitGenNode (btSort tm) (fbAppGen fb) storedArgs [] [fPort, aPort] d1
        Nothing ->
          Left "defeq: cannot quote application without function-space builtins"
  where
    buildHeadArgForCtx arg =
      case arg of
        BHAObj obj -> Right (CAObj obj)
        BHATm tmArg -> do
          let argMode = objOwnerMode (btSort tmArg)
          let argFragment =
                case defFragmentForMode tt argMode of
                  Just fragment' -> fragment'
                  Nothing -> fragment
          let modeInputsAll = modeCtx (bcTmCtx ctx) argMode
          needed <- requiredTopPrefix tmArg
          if needed <= length modeInputsAll
            then Right ()
            else Left "NbE: stored term argument requires larger mode-local context prefix than available"
          let inSorts = map snd (take needed modeInputsAll)
          tmDiag <- btmToDiagram tt argFragment (bcTmCtx ctx) (btSort tmArg) inSorts tmArg
          Right (CATm (TermDiagram tmDiag))

    buildBinderArg arg =
      case arg of
        BBABody inner -> BAConcrete inner
        BBAHole hole -> BAMeta hole

requiredTopPrefix :: BTm -> Either Text Int
requiredTopPrefix tm = go 0 tm
  where
    go depth t =
      case btExpr t of
        BVar i ->
          if i < depth
            then Right 0
            else Right (i - depth + 1)
        BMeta v args -> do
          reqArgs <- mapM (argReq depth) args
          pure (max (maximumOrZero reqArgs) (max 0 (tmvScope v - depth)))
        BGen _ headArgs args -> do
          reqHead <- mapM (headReq depth) headArgs
          reqArgs <- mapM (go depth) args
          pure (maximumOrZero (reqHead <> reqArgs))
        BBind _ headArgs args _ -> do
          reqHead <- mapM (headReq depth) headArgs
          reqArgs <- mapM (go depth) args
          pure (maximumOrZero (reqHead <> reqArgs))
        BResidual residual ->
          Right (length (dIn residual))
        BSplice _ _ args -> do
          reqArgs <- mapM (go depth) args
          pure (maximumOrZero reqArgs)
        BLit _ ->
          Right 0
        BLam headArgs body -> do
          rh <- mapM (headReq depth) headArgs
          rb <- go (depth + 1) body
          pure (max rb (maximumOrZero rh))
        BApp headArgs f a -> do
          rh <- mapM (headReq depth) headArgs
          rf <- go depth f
          ra <- go depth a
          pure (maximumOrZero (rh <> [rf, ra]))

    argReq depth i =
      if i < depth
        then Right 0
        else Right (i - depth + 1)

    headReq depth arg =
      case arg of
        BHAObj _ -> Right 0
        BHATm tmArg -> go depth tmArg

mkInitialEnv :: Int -> [Obj] -> Either Text [Val]
mkInitialEnv lvl inSortsOldToNew = do
  let nearest = reverse inSortsOldToNew
  pure
    [ neutralVar (lvl - 1 - i) sortTy
    | (i, sortTy) <- zip [0 :: Int ..] nearest
    ]

neutralVar :: Int -> Obj -> Val
neutralVar level sortTy =
  Val
    { valSort = sortTy
    , valExpr = VNeu (NVar level sortTy)
    }

metaArgIndex :: Int -> Val -> Either Text Int
metaArgIndex lvl argVal =
  case valExpr argVal of
    VNeu (NVar level _) ->
      let idx = lvl - level - 1
       in if idx >= 0
            then Right idx
            else Left "NbE: invalid metavariable argument level"
    _ ->
      Left "NbE: metavariable arguments must remain neutral variables"

metaArgPort :: BuildCtx -> Int -> Either Text PortId
metaArgPort ctx i =
  case nth (bcVarsNearest ctx) i of
    Just (_, pid) -> Right pid
    Nothing -> Left "NbE: metavariable argument index out of scope"

splitArr :: DefFragment -> Obj -> Maybe (Obj, Obj)
splitArr fragment ty = do
  fb <- functionBuiltin fragment
  case objCode ty of
    CTCon (ObjRef _ name) [CAObj domTy, CAObj codTy]
      | name == fbArrTyCon fb -> Just (domTy, codTy)
    _ -> Nothing

synthArrHeadArgs :: DefFragment -> Obj -> [BTmHeadArg]
synthArrHeadArgs fragment ty =
  case splitArr fragment ty of
    Just (domTy, codTy) -> [BHAObj domTy, BHAObj codTy]
    Nothing -> []

synthAppHeadArgs :: Obj -> Obj -> [ValHeadArg]
synthAppHeadArgs domTy codTy =
  [ VHAObj domTy
  , VHAObj codTy
  ]

functionBuiltin :: DefFragment -> Maybe FunctionBuiltin
functionBuiltin = bhFunctionSpace . dfBuiltins

extensionalBuiltin :: DefFragment -> GenName -> Maybe ExtensionalBuiltin
extensionalBuiltin fragment g =
  M.lookup g (bhExtensionalHeads (dfBuiltins fragment))

eliminatorBuiltin :: DefFragment -> GenName -> Maybe EliminatorBuiltin
eliminatorBuiltin fragment g =
  M.lookup g (bhEliminators (dfBuiltins fragment))

valueToTermDiagram
  :: DefFragment
  -> TypeTheory
  -> TermConvEnv
  -> [Obj]
  -> Int
  -> Obj
  -> Val
  -> Either Text TermDiagram
valueToTermDiagram fragment tt convEnv tmCtx sortLvl sortTy val = do
  btm <- quoteValAtSort fragment tt convEnv tmCtx sortLvl sortTy val
  let modeInputsAll = modeCtx tmCtx (objOwnerMode sortTy)
  needed <- requiredTopPrefix btm
  if needed <= length modeInputsAll
    then pure ()
    else Left "defeq: quoted trusted rewrite argument requires larger mode-local context prefix than available"
  let inSorts = map snd (take needed modeInputsAll)
  TermDiagram <$> btmToDiagram tt fragment tmCtx sortTy inSorts btm

requirePortSort :: Diagram -> Text -> PortId -> Either Text Obj
requirePortSort diag label pid =
  case diagramPortObj diag pid of
    Just ty -> Right ty
    Nothing -> Left label

hasImmediateStructuralPayload :: Diagram -> Bool
hasImmediateStructuralPayload diag =
  any isStructuralEdge (IM.elems (dEdges diag))
  where
    isStructuralEdge edge =
      case ePayload edge of
        PProvider _ -> True
        PModuleRef _ -> True
        PBox _ _ -> True
        PFeedback _ -> True
        _ -> False

normalizeResidualDiagramPayloads
  :: TypeTheory
  -> TermConvEnv
  -> Diagram
  -> Either Text Diagram
normalizeResidualDiagramPayloads tt convEnv diag0 = do
  diag1 <- traverseDiagram onDiag pure onCodeArg onBinderArg diag0
  validateDiagram diag1
  canonDiagramRaw diag1
  where
    onDiag diag = do
      validateDiagram diag
      pure diag

    onCodeArg arg =
      case arg of
        CAObj _ ->
          Right arg
        CATm (TermDiagram inner) -> do
          norm <- normalizeEmbeddedTermDiagram "NbE: structural residual code arg" inner
          pure (CATm norm)

    onBinderArg barg =
      case barg of
        BAMeta _ ->
          Right barg
        BAConcrete inner -> do
          norm <- normalizeEmbeddedTermDiagram "NbE: structural residual binder body" inner
          pure (BAConcrete (unTerm norm))

    normalizeEmbeddedTermDiagram label inner = do
      expectedSort <- requireSingleOutputSort label inner
      boundarySorts <- mapM (requirePortSort inner (label <> ": missing boundary input sort")) (dIn inner)
      innerFragment <-
        case defFragmentForMode tt (objOwnerMode expectedSort) of
          Just one -> Right one
          Nothing -> Left (label <> ": missing definitional fragment for nested term diagram")
      normalizeDiagramDefEqAgainst innerFragment tt convEnv (dTmCtx inner) boundarySorts expectedSort inner

requireSingleOutputSort :: Text -> Diagram -> Either Text Obj
requireSingleOutputSort label diag =
  case dOut diag of
    [pid] -> requirePortSort diag (label <> ": missing output sort") pid
    _ -> Left (label <> ": term diagram must have exactly one output")

setResidualInterfaceSorts :: [Obj] -> Obj -> Diagram -> Either Text Diagram
setResidualInterfaceSorts boundarySorts expectedSort diag = do
  if length boundarySorts == length (dIn diag)
    then pure ()
    else Left "NbE: residual interface arity mismatch"
  outPid <-
    case dOut diag of
      [pid] -> Right pid
      _ -> Left "NbE: residual term diagram must have exactly one output"
  let portObj' =
        foldl
          (\acc (pid, sortTy) -> IM.insert (unPortId pid) sortTy acc)
          (IM.insert (unPortId outPid) expectedSort (dPortObj diag))
          (zip (dIn diag) boundarySorts)
  pure diag { dPortObj = portObj' }

embedResidualDiagram
  :: BuildCtx
  -> Diagram
  -> Obj
  -> Diagram
  -> Either Text (PortId, Diagram)
embedResidualDiagram ctx host expectedSort residual = do
  let needed = length (dIn residual)
  if needed <= length (bcBoundaryOldToNew ctx)
    then pure ()
    else Left "NbE: residual diagram requires larger boundary context prefix than available during quoting"
  boundarySorts <- mapM (requirePortSort host "NbE: quoting residual diagram is missing a boundary sort") (take needed (bcBoundaryOldToNew ctx))
  let shifted0 = shiftDiagram (dNextPort host) (dNextEdge host) residual
  shifted <- setResidualInterfaceSorts boundarySorts expectedSort shifted0
  merged0 <- unionDiagramRaw host shifted
  merged <-
    foldM
      (\d (targetPid, residualPid) -> mergePorts d targetPid residualPid)
      merged0
      (zip (take needed (bcBoundaryOldToNew ctx)) (dIn shifted))
  outPid0 <-
    case dOut shifted of
      [pid] -> Right pid
      _ -> Left "NbE: residual term diagram must have exactly one output during quoting"
  let outPid =
        foldl
          (\pid (residualPid, targetPid) -> if pid == residualPid then targetPid else pid)
          outPid0
          (zip (dIn shifted) (take needed (bcBoundaryOldToNew ctx)))
  pure (outPid, merged)

unionDiagramRaw :: Diagram -> Diagram -> Either Text Diagram
unionDiagramRaw left right
  | dMode left /= dMode right = Left "NbE: residual diagram mode mismatch during quoting"
  | dTmCtx left /= dTmCtx right = Left "NbE: residual diagram term-context mismatch during quoting"
  | otherwise = do
      portTy <- unionDisjointIntMap "NbE residual ports" (dPortObj left) (dPortObj right)
      portLabel <- unionDisjointIntMap "NbE residual labels" (dPortLabel left) (dPortLabel right)
      prod <- unionDisjointIntMap "NbE residual producers" (dProd left) (dProd right)
      cons <- unionDisjointIntMap "NbE residual consumers" (dCons left) (dCons right)
      edges <- unionDisjointIntMap "NbE residual edges" (dEdges left) (dEdges right)
      pure
        Diagram
          { dMode = dMode left
          , dTmCtx = dTmCtx left
          , dIn = dIn left <> dIn right
          , dOut = dOut left <> dOut right
          , dPortObj = portTy
          , dPortLabel = portLabel
          , dProd = prod
          , dCons = cons
          , dEdges = edges
          , dNextPort = max (dNextPort left) (dNextPort right)
          , dNextEdge = max (dNextEdge left) (dNextEdge right)
          }

maximumOrZero :: [Int] -> Int
maximumOrZero [] = 0
maximumOrZero xs = maximum xs

nth :: [a] -> Int -> Maybe a
nth xs i
  | i < 0 = Nothing
  | otherwise =
      case drop i xs of
        (y:_) -> Just y
        [] -> Nothing
