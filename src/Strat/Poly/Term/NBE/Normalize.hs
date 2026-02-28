{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.NBE.Normalize
  ( normalizeDiagramNBE
  ) where

import Control.Monad (foldM)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Graph
  ( Diagram(..)
  , PortId
  , Edge(..)
  , EdgePayload(..)
  , BinderArg(..)
  , addEdgePayload
  , canonDiagramRaw
  , diagramPortObj
  , emptyDiagram
  , freshPort
  , unPortId
  , unEdgeId
  , validateDiagram
  )
import Strat.Poly.Obj
  ( Obj(..)
  , ObjRef(..)
  , TermDiagram(..)
  , TmVar(..)
  , modeCtx
  , CodeArg(..)
  , CodeTerm(..)
  , objOwnerMode
  )
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeTheory (TypeTheory)
import Strat.Poly.Term.NBE.Config (NbeConfig(..))

type SortEq = [Obj] -> Obj -> Obj -> Either Text Bool

data BTm = BTm
  { btSort :: Obj
  , btExpr :: BTmExpr
  } deriving (Eq, Show)

data BTmExpr
  = BVar Int
  | BMeta TmVar [Int]
  | BGen GenName [BTm]
  | BLam BTm
  | BApp BTm BTm
  deriving (Eq, Show)

data Val = Val
  { valSort :: Obj
  , valExpr :: ValExpr
  }

data ValExpr
  = VLam (Val -> Either Text Val)
  | VNeu Neu

data Neu
  = NVar Int Obj
  | NMeta TmVar [Val]
  | NGen GenName [Val] Obj
  | NApp Neu Val Obj Obj

normalizeDiagramNBE
  :: NbeConfig
  -> TypeTheory
  -> SortEq
  -> [Obj]
  -> Obj
  -> Diagram
  -> Either Text TermDiagram
normalizeDiagramNBE cfg tt sortEq tmCtx expectedSort src = do
  rejectUnsupportedDiagram cfg src
  case dOut src of
    [_] -> Right ()
    _ -> Left "NbE: term diagram must have exactly one output"
  let mode = dMode src
  let modeInputsAll = modeCtx tmCtx mode
  let nIn = length (dIn src)
  if nIn <= length modeInputsAll
    then Right ()
    else Left "NbE: boundary input prefix exceeds mode-local context"
  srcInSorts <- mapM (requirePortSort src "NbE: missing boundary input sort") (dIn src)
  tm <- diagramToBTm cfg sortEq src [nIn - 1, nIn - 2 .. 0] expectedSort
  let lvl0 = nIn
  env <- mkInitialEnv lvl0 srcInSorts
  val <- evalBTm cfg tt env tm
  nf <- reify cfg tt lvl0 expectedSort val
  needed <- requiredTopPrefix nf
  if needed <= length modeInputsAll
    then Right ()
    else Left "NbE: normalized term requires larger mode-local context prefix than available"
  let neededInSorts = map snd (take needed modeInputsAll)
  out <- btmToDiagram cfg tmCtx expectedSort neededInSorts nf
  validateDiagram out
  outCanon <- canonDiagramRaw out
  validateDiagram outCanon
  pure (TermDiagram outCanon)

diagramToBTm :: NbeConfig -> SortEq -> Diagram -> [Int] -> Obj -> Either Text BTm
diagramToBTm cfg sortEq diag boundaryVars expectedSort = do
  validateDiagram diag
  case dOut diag of
    [out] -> do
      outTy <- requirePortSort diag "NbE: missing output sort" out
      boundarySorts <- boundarySortsForDiag
      sortMatches <- sortEq boundarySorts outTy expectedSort
      if sortMatches
        then termAt S.empty out
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

    boundarySortsForDiag =
      mapM (requirePortSort diag "NbE: missing boundary input sort") (dIn diag)

    termAt seen pid =
      case M.lookup pid inMap of
        Just localIx ->
          case nth boundaryVars localIx of
            Nothing -> Left "NbE: invalid boundary-variable mapping"
            Just idx -> do
              sortTy <- requirePortSort diag "NbE: missing boundary sort" pid
              pure BTm { btSort = sortTy, btExpr = BVar idx }
        Nothing ->
          if pid `S.member` seen
            then Left "NbE: cycle detected in term diagram"
            else do
              edge <- producerEdge pid
              let seen' = S.insert pid seen
              case ePayload edge of
                PGen g attrs bargs ->
                  if not (M.null attrs)
                    then Left "NbE: generator attrs are unsupported in NbE definitional normalization"
                    else
                      if g == nbeLamGen cfg
                        then parseLam pid edge bargs
                        else
                          if g == nbeAppGen cfg
                            then parseApp seen' pid edge bargs
                            else do
                              if null bargs
                                then Right ()
                                else Left "NbE: non-lam generators with binder args are unsupported in NbE"
                              args <- mapM (termAt seen') (eIns edge)
                              sortTy <- requirePortSort diag "NbE: missing generator output sort" pid
                              pure BTm { btSort = sortTy, btExpr = BGen g args }
                PTmMeta v -> do
                  sortTy <- requirePortSort diag "NbE: missing PTmMeta output sort" pid
                  let v' = v { tmvSort = sortTy }
                  metaArgs <- mapM boundaryVarIndex (eIns edge)
                  pure BTm { btSort = sortTy, btExpr = BMeta v' metaArgs }
                PInternalDrop ->
                  Left "NbE: reachable PInternalDrop is unsupported in NbE term normalization"
                PBox _ _ ->
                  Left "NbE: box nodes are unsupported in NbE definitional normalization"
                PFeedback _ ->
                  Left "NbE: feedback nodes are unsupported in NbE definitional normalization"
                PSplice _ ->
                  Left "NbE: splice nodes are unsupported in NbE definitional normalization"

    producerEdge pid =
      case IM.lookup (unPortId pid) (dProd diag) of
        Just (Just eid) ->
          case IM.lookup (unEdgeId eid) (dEdges diag) of
            Just edge -> Right edge
            Nothing -> Left "NbE: missing producer edge"
        _ -> Left "NbE: missing producer edge"

    boundaryVarIndex pid =
      case M.lookup pid inMap of
        Just local ->
          case nth boundaryVars local of
            Just idx -> Right idx
            Nothing -> Left "NbE: boundary-variable mapping failure"
        Nothing ->
          Left "NbE: PTmMeta inputs must connect to boundary ports"

    parseLam pid edge bargs = do
      case (eIns edge, eOuts edge, bargs) of
        ([], [outPid], [BAConcrete bodyDiag])
          | outPid == pid -> do
              lamSort <- requirePortSort diag "NbE: missing lambda output sort" outPid
              (domTy, codTy) <-
                case splitArr cfg lamSort of
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
              bodyDomMatches <- sortEq bodyInSorts firstBodyTy domTy
              if bodyDomMatches
                then Right ()
                else Left "NbE: lambda binder body bound-variable sort mismatch"
              body <- diagramToBTm cfg sortEq bodyDiag bodyBoundaryVars codTy
              pure BTm { btSort = lamSort, btExpr = BLam body }
        _ ->
          Left "NbE: lam node must have no plain inputs, one output, and one concrete binder body"

    parseApp seen pid edge bargs = do
      case (eIns edge, eOuts edge, bargs) of
        ([fIn, aIn], [outPid], [])
          | outPid == pid -> do
              fTm <- termAt seen fIn
              aTm <- termAt seen aIn
              outTy <- requirePortSort diag "NbE: missing app output sort" outPid
              case splitArr cfg (btSort fTm) of
                Just (domTy, codTy) -> do
                  boundarySorts <- boundarySortsForDiag
                  domMatches <- sortEq boundarySorts domTy (btSort aTm)
                  codMatches <- sortEq boundarySorts codTy outTy
                  if domMatches && codMatches
                    then pure BTm { btSort = outTy, btExpr = BApp fTm aTm }
                    else Left "NbE: app node type mismatch against Arr(domain, codomain)"
                Nothing ->
                  Left "NbE: app function input does not have Arr type"
        _ ->
          Left "NbE: app node must have exactly two inputs, one output, and no binder args"

evalBTm :: NbeConfig -> TypeTheory -> [Val] -> BTm -> Either Text Val
evalBTm cfg tt env tm =
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
    BGen g args -> do
      vals <- mapM (evalBTm cfg tt env) args
      Right
        Val
          { valSort = btSort tm
          , valExpr = VNeu (NGen g vals (btSort tm))
          }
    BLam body ->
      Right
        Val
          { valSort = btSort tm
          , valExpr =
              VLam
                ( \v ->
                    evalBTm cfg tt (v : env) body
                )
          }
    BApp f a -> do
      fV <- evalBTm cfg tt env f
      aV <- evalBTm cfg tt env a
      applyVal cfg tt fV aV
  where
    lookupArg i =
      case nth env i of
        Just v -> Right v
        Nothing -> Left "NbE: metavariable argument index out of scope during evaluation"

applyVal :: NbeConfig -> TypeTheory -> Val -> Val -> Either Text Val
applyVal cfg _tt funVal argVal =
  case valExpr funVal of
    VLam f -> f argVal
    VNeu n ->
      case splitArr cfg (valSort funVal) of
        Just (domTy, codTy)
          | domTy == valSort argVal ->
              Right
                Val
                  { valSort = codTy
                  , valExpr = VNeu (NApp n argVal domTy codTy)
                  }
          | otherwise ->
              Left "NbE: neutral application argument sort mismatch"
        Nothing ->
          Left "NbE: attempted to apply a non-function neutral"

reify :: NbeConfig -> TypeTheory -> Int -> Obj -> Val -> Either Text BTm
reify cfg tt lvl expectedSort val =
  case splitArr cfg expectedSort of
    Just (domTy, codTy)
      | nbeAllowEta cfg -> do
          let fresh = neutralVar lvl domTy
          bodyVal <- applyVal cfg tt val fresh
          body <- reify cfg tt (lvl + 1) codTy bodyVal
          pure BTm { btSort = expectedSort, btExpr = BLam body }
    _ ->
      quoteVal lvl val
  where
    quoteVal lvl0 v =
      case valExpr v of
        VNeu n -> quoteNeu cfg lvl0 n
        VLam f ->
          case splitArr cfg expectedSort of
            Just (domTy, codTy) -> do
              let fresh = neutralVar lvl0 domTy
              bodyVal <- f fresh
              body <- reify cfg tt (lvl0 + 1) codTy bodyVal
              pure BTm { btSort = expectedSort, btExpr = BLam body }
            Nothing ->
              Left "NbE: cannot quote lambda at non-function expected sort"

quoteNeu :: NbeConfig -> Int -> Neu -> Either Text BTm
quoteNeu cfg lvl neu =
  case neu of
    NVar level sortTy -> do
      let idx = lvl - level - 1
      if idx >= 0
        then pure BTm { btSort = sortTy, btExpr = BVar idx }
        else Left "NbE: internal level/index conversion underflow"
    NMeta v args -> do
      argIdx <- mapM (metaArgIndex lvl) args
      pure BTm { btSort = tmvSort v, btExpr = BMeta v argIdx }
    NGen g args sortTy -> do
      args' <- mapM (\v -> quoteValAt lvl v) args
      pure BTm { btSort = sortTy, btExpr = BGen g args' }
    NApp f a domTy codTy -> do
      f' <- quoteNeu cfg lvl f
      a' <- quoteAtSort lvl domTy a
      pure BTm { btSort = codTy, btExpr = BApp f' a' }
  where
    quoteValAt lvl0 v =
      quoteAtSort lvl0 (valSort v) v

    quoteAtSort lvl0 sortTy v =
      case valExpr v of
        VNeu n -> quoteNeu cfg lvl0 n
        VLam f ->
          case splitArr cfg sortTy of
            Just (domTy, codTy) -> do
              let fresh = neutralVar lvl0 domTy
              bodyVal <- f fresh
              body <- quoteAtSort (lvl0 + 1) codTy bodyVal
              pure BTm { btSort = sortTy, btExpr = BLam body }
            Nothing ->
              Left "NbE: cannot quote lambda at non-function sort"

btmToDiagram
  :: NbeConfig
  -> [Obj]
  -> Obj
  -> [Obj]
  -> BTm
  -> Either Text Diagram
btmToDiagram cfg tmCtx expectedSort inSorts tm = do
  let mode = objOwnerMode expectedSort
  let (inPorts, d0) = allocPorts inSorts (emptyDiagram mode tmCtx)
  let varsNearest = reverse (zip inSorts inPorts)
  let ctx0 =
        BuildCtx
          { bcMode = mode
          , bcTmCtx = tmCtx
          , bcVarsNearest = varsNearest
          , bcBoundaryOldToNew = inPorts
          }
  (outPort, d1) <- buildBTm cfg ctx0 d0 tm
  let d2 = d1 { dIn = inPorts, dOut = [outPort] }
  saturateUnusedInputs d2

data BuildCtx = BuildCtx
  { bcMode :: ModeName
  , bcTmCtx :: [Obj]
  , bcVarsNearest :: [(Obj, PortId)]
  , bcBoundaryOldToNew :: [PortId]
  }

buildBTm :: NbeConfig -> BuildCtx -> Diagram -> BTm -> Either Text (PortId, Diagram)
buildBTm cfg ctx diag tm =
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
      let (out, d0) = freshPort (btSort tm) diag
      d1 <- addEdgePayload (PTmMeta v') argPorts [out] d0
      pure (out, d1)
    BGen g args -> do
      (argPorts, d0) <- foldM step ([], diag) args
      let (out, d1) = freshPort (btSort tm) d0
      d2 <- addEdgePayload (PGen g M.empty []) argPorts [out] d1
      pure (out, d2)
      where
        step (ports, dAcc) arg = do
          (pid, dNext) <- buildBTm cfg ctx dAcc arg
          pure (ports <> [pid], dNext)
    BLam body -> do
      (domTy, _codTy) <-
        case splitArr cfg (btSort tm) of
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
      (innerOut, innerBuilt0) <- buildBTm cfg innerCtx inner0 body
      let innerBuilt1 = innerBuilt0 { dIn = innerInPorts, dOut = [innerOut] }
      innerBuilt <- saturateUnusedInputs innerBuilt1
      validateDiagram innerBuilt
      let (out, d0) = freshPort (btSort tm) diag
      d1 <- addEdgePayload (PGen (nbeLamGen cfg) M.empty [BAConcrete innerBuilt]) [] [out] d0
      pure (out, d1)
    BApp f a -> do
      (fPort, d0) <- buildBTm cfg ctx diag f
      (aPort, d1) <- buildBTm cfg ctx d0 a
      let (out, d2) = freshPort (btSort tm) d1
      d3 <- addEdgePayload (PGen (nbeAppGen cfg) M.empty []) [fPort, aPort] [out] d2
      pure (out, d3)

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
        BGen _ args ->
          maximumOrZero <$> mapM (go depth) args
        BLam body ->
          go (depth + 1) body
        BApp f a -> do
          rf <- go depth f
          ra <- go depth a
          pure (max rf ra)

    argReq depth i =
      if i < depth
        then Right 0
        else Right (i - depth + 1)

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

splitArr :: NbeConfig -> Obj -> Maybe (Obj, Obj)
splitArr cfg ty =
  case objCode ty of
    CTCon (ObjRef _ name) [CAObj domTy, CAObj codTy]
      | name == nbeArrTyCon cfg -> Just (domTy, codTy)
    _ -> Nothing

rejectUnsupportedDiagram :: NbeConfig -> Diagram -> Either Text ()
rejectUnsupportedDiagram cfg diag = do
  validateDiagram diag
  mapM_ checkEdge (IM.elems (dEdges diag))
  where
    checkEdge edge =
      case ePayload edge of
        PGen _ attrs bargs ->
          if M.null attrs
            then mapM_ checkBinderArg bargs
            else Left "NbE: generator attrs are unsupported in definitional normalization"
        PTmMeta _ -> Right ()
        PInternalDrop -> Right ()
        PBox _ _ -> Left "NbE: box nodes are unsupported in definitional normalization"
        PFeedback _ -> Left "NbE: feedback nodes are unsupported in definitional normalization"
        PSplice _ -> Left "NbE: splice nodes are unsupported in definitional normalization"

    checkBinderArg barg =
      case barg of
        BAConcrete inner -> rejectUnsupportedDiagram cfg inner
        BAMeta _ -> Left "NbE: binder metavariables are unsupported in definitional normalization"

saturateUnusedInputs :: Diagram -> Either Text Diagram
saturateUnusedInputs diag =
  foldM step diag (dIn diag)
  where
    step d pid =
      let boundaryOutput = pid `elem` dOut d
       in case IM.lookup (unPortId pid) (dCons d) of
            Just Nothing
              | boundaryOutput -> Right d
              | otherwise -> addEdgePayload PInternalDrop [pid] [] d
            _ -> Right d

requirePortSort :: Diagram -> Text -> PortId -> Either Text Obj
requirePortSort diag label pid =
  case diagramPortObj diag pid of
    Just ty -> Right ty
    Nothing -> Left label

allocPorts :: [Obj] -> Diagram -> ([PortId], Diagram)
allocPorts [] d = ([], d)
allocPorts (ty:rest) d =
  let (pid, d1) = freshPort ty d
      (restPids, d2) = allocPorts rest d1
   in (pid : restPids, d2)

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
