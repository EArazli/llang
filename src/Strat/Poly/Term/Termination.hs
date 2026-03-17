{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Term.Termination
  ( checkTerminatingSCT
  , renderSCTDebug
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.List as L
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Syntax
  ( BinderArg(..)
  , CodeArg(..)
  , Diagram(..)
  , Edge(..)
  , EdgeId(..)
  , EdgePayload(..)
  , TermDiagram(..)
  , mkModeMetaVar
  , unEdgeId
  , unPortId
  )
import Strat.Poly.Term.AST (TermBinderArg(..), TermExpr(..), TermHeadArg(..))
import Strat.Poly.Term.RewriteSystem (TRS(..), TRule(..), maxBoundVarIndex)


data SCRel
  = SCStrict
  | SCWeak
  deriving (Eq, Ord, Show)

data SCGraph = SCGraph
  { scFrom :: GenName
  , scTo :: GenName
  , scHidden :: Bool
  , scFromArity :: Int
  , scToArity :: Int
  , scEdges :: M.Map (Int, Int) SCRel
  } deriving (Eq, Ord, Show)

data CallSite = CallSite
  { csHidden :: Bool
  , csHead :: GenName
  , csArgs :: [TermHeadArg]
  }


checkTerminatingSCT :: TRS -> Either Text ()
checkTerminatingSCT trs = do
  base <- buildBaseGraphs trs
  let closure = closureGraphs base
  let idempotent = filter isIdempotent (S.toList closure)
  let bad = filter (not . hasStrictSelfLoop) idempotent
  if null bad
    then Right ()
    else
      Left
        ( "termination not proven by SCT for mode "
            <> renderMode trs
            <> ": found idempotent call graph without strict self-decrease\n"
            <> renderGraphs bad
        )

renderSCTDebug :: TRS -> Text
renderSCTDebug trs =
  case buildBaseGraphs trs of
    Left err -> "SCT build failed: " <> err
    Right base ->
      let closure = closureGraphs base
       in T.unlines
            [ "SCT debug for mode " <> renderMode trs
            , "base graphs:"
            , indent (renderGraphs (S.toList (S.fromList base)))
            , "closure graphs:"
            , indent (renderGraphs (S.toList closure))
            ]


buildBaseGraphs :: TRS -> Either Text [SCGraph]
buildBaseGraphs trs = concat <$> mapM ruleGraphs (trsRules trs)

ruleGraphs :: TRule -> Either Text [SCGraph]
ruleGraphs rule = do
  (f, lhsArgs) <-
    case trLHS rule of
      TMHead fn args _ -> Right (fn, args)
      _ -> Left ("termination checker requires function-headed lhs in rule " <> trName rule)
  calls <-
    case trRHS rule of
      Just rhsExpr -> do
        let binderBase = 1 + max (maxBoundVarIndex (trLHS rule)) (maxBoundVarIndex rhsExpr)
        collectCalls binderBase False rhsExpr
      Nothing ->
        case trRHSDiagram rule of
          Just (TermDiagram rhsDiag) ->
            collectDiagramCalls rhsDiag
          Nothing ->
            Left ("termination checker requires a rhs in rule " <> trName rule)
  pure
    [ mkGraph f lhsArgs (csHead callSite) (csArgs callSite) (csHidden callSite)
    | callSite <- calls
    ]

collectDiagramCalls :: Diagram -> Either Text [CallSite]
collectDiagramCalls =
  collectDiagramCallsWith 0 False

collectDiagramCallsWith :: Int -> Bool -> Diagram -> Either Text [CallSite]
collectDiagramCallsWith boundaryBase hidden diag =
  fmap concat (mapM edgeCalls (IM.elems (dEdges diag)))
  where
    inMap = M.fromList (zip (dIn diag) [0 :: Int ..])

    edgeCalls edge =
      case ePayload edge of
        PGen f args bargs -> do
          storedArgs <- mapM decodeCodeArg args
          inputArgs <- mapM decodeInput (eIns edge)
          storedCalls <- fmap concat (mapM codeArgCalls args)
          let binderBase = nextBinderBase (storedArgs <> inputArgs)
          binderCalls <- fmap concat (mapM (binderCallsForArg binderBase) bargs)
          pure
            ( CallSite
                { csHidden = hidden
                , csHead = f
                , csArgs = storedArgs <> inputArgs
                }
                : storedCalls
                <> binderCalls
            )
        PProvider _ ->
          pure []
        PModuleRef _ ->
          pure []
        PBox _ inner ->
          collectDiagramCallsWith boundaryBase True inner
        PFeedback inner ->
          collectDiagramCallsWith boundaryBase True inner
        PTmMeta _ ->
          pure []
        PTmLit _ ->
          pure []
        PInternalDrop ->
          pure []
        PSplice _ _ ->
          pure []

    decodeInput pid =
      THATm <$> readPort S.empty pid

    readPort seen pid =
      case M.lookup pid inMap of
        Just local ->
          Right (TMBound (boundaryBase + local))
        Nothing ->
          if pid `S.member` seen
            then Left "termination checker: cycle detected in structural rhs"
            else do
              edge <- producerEdge pid
              buildEdge (S.insert pid seen) edge

    producerEdge pid =
      case IM.lookup (unPortId pid) (dProd diag) of
        Just (Just eid) ->
          case IM.lookup (unEdgeId eid) (dEdges diag) of
            Just edge -> Right edge
            Nothing -> Left "termination checker: missing producer in structural rhs"
        _ ->
          Left "termination checker: missing producer in structural rhs"

    buildEdge seen edge =
      case ePayload edge of
        PGen f args bargs -> do
          storedArgs <- mapM decodeCodeArg args
          inputArgs <- mapM (decodeInputSeen seen) (eIns edge)
          binderArgs <- mapM decodeBinderArg bargs
          Right (TMHead f (storedArgs <> inputArgs) binderArgs)
        PSplice hole me -> do
          args <- mapM (readPort seen) (eIns edge)
          Right (TMSplice hole me args)
        PProvider _ ->
          Right (opaqueEdgeTerm "provider" edge)
        PModuleRef _ ->
          Right (opaqueEdgeTerm "module_ref" edge)
        PBox _ _ ->
          Right (opaqueEdgeTerm "box" edge)
        PFeedback _ ->
          Right (opaqueEdgeTerm "feedback" edge)
        PTmMeta v -> do
          metaArgs <- mapM boundaryLocal (eIns edge)
          Right (TMMeta v metaArgs)
        PTmLit lit ->
          Right (TMLit lit)
        PInternalDrop ->
          Right (opaqueEdgeTerm "drop" edge)

    decodeInputSeen seen pid =
      THATm <$> readPort seen pid

    decodeCodeArg arg =
      case arg of
        CAObj obj -> Right (THAObj obj)
        CATm tm -> do
          expr <- termDiagramExpr tm
          Right (THATm expr)

    codeArgCalls arg =
      case arg of
        CAObj _ ->
          pure []
        CATm (TermDiagram inner) -> do
          expr <- termDiagramExpr (TermDiagram inner)
          exprCalls <- collectCalls boundaryBase hidden expr
          if diagramHasStructuralPayload inner
            then do
              innerCalls <- collectDiagramCallsWith boundaryBase hidden inner
              pure (exprCalls <> innerCalls)
            else pure exprCalls

    binderCallsForArg binderBase barg =
      case barg of
        BAConcrete inner ->
          collectDiagramCallsWith binderBase True inner
        BAMeta _ ->
          pure []

    decodeBinderArg barg =
      case barg of
        BAConcrete inner -> Right (TBABody inner)
        BAMeta hole -> Right (TBAHole hole)

    boundaryLocal pid =
      case M.lookup pid inMap of
        Just local -> Right (boundaryBase + local)
        Nothing -> Left "termination checker: PTmMeta inputs in structural rhs must connect to boundary inputs"

    termDiagramExpr (TermDiagram inner) =
      case dOut inner of
        [_] -> do
          terms <- diagramOutputTerms boundaryBase inner
          case terms of
            [term] -> Right term
            _ -> Left "termination checker: stored term arguments must have exactly one output"
        _ ->
          Left "termination checker: stored term arguments must have exactly one output"

    nextBinderBase args =
      1 + maximum (-1 : map maxHeadArgBound args)

    maxHeadArgBound arg =
      case arg of
        THAObj _ -> -1
        THATm tm -> maxBoundVarIndex tm

    opaqueEdgeTerm tag edge =
      TMMeta
        (mkModeMetaVar ("__sct_" <> tag <> "_" <> renderEdgeId (eId edge)) (dMode diag))
        []

diagramHasStructuralPayload :: Diagram -> Bool
diagramHasStructuralPayload =
  any edgeIsStructural . IM.elems . dEdges
  where
    edgeIsStructural edge =
      case ePayload edge of
        PProvider _ -> True
        PModuleRef _ -> True
        PBox _ _ -> True
        PFeedback _ -> True
        PInternalDrop -> True
        _ -> False

collectCalls :: Int -> Bool -> TermExpr -> Either Text [CallSite]
collectCalls binderBase hidden tm =
  case tm of
    TMHead f args bargs -> do
      argCalls <- fmap concat (mapM (collectHeadArgCalls binderBase hidden) args)
      binderCalls <- fmap concat (mapM (collectBinderCalls binderBase) bargs)
      pure
        ( CallSite
            { csHidden = hidden
            , csHead = f
            , csArgs = args
            }
            : argCalls
            <> binderCalls
        )
    TMSplice _ _ args ->
      fmap concat (mapM (collectCalls binderBase hidden) args)
    TMMeta _ _ -> pure []
    TMBound _ -> pure []
    TMLit _ -> pure []

collectHeadArgCalls :: Int -> Bool -> TermHeadArg -> Either Text [CallSite]
collectHeadArgCalls binderBase hidden arg =
  case arg of
    THAObj _ -> pure []
    THATm tm -> collectCalls binderBase hidden tm

collectBinderCalls :: Int -> TermBinderArg -> Either Text [CallSite]
collectBinderCalls binderBase barg =
  case barg of
    TBABody inner ->
      collectDiagramCallsWith binderBase True inner
    TBAHole _ ->
      pure []

mkGraph :: GenName -> [TermHeadArg] -> GenName -> [TermHeadArg] -> Bool -> SCGraph
mkGraph f lhsArgs g qArgs hidden =
  SCGraph
    { scFrom = f
    , scTo = g
    , scHidden = hidden
    , scFromArity = length lhsTerms
    , scToArity = length qTerms
    , scEdges = edgeMap
    }
  where
    lhsTerms = [ tm | THATm tm <- lhsArgs ]
    qTerms = [ tm | THATm tm <- qArgs ]

    edgeMap =
      M.fromList
        [ ((i, j), rel)
        | (i, p) <- zip [0 :: Int ..] lhsTerms
        , (j, q) <- zip [0 :: Int ..] qTerms
        , Just rel <- [edgeRel binderBase p q]
        ]

    binderBase = 1 + maximum (-1 : map maxBoundVarIndex (lhsTerms <> qTerms))

    edgeRel base tmP tmQ
      | strictSubterm base tmQ tmP = Just SCStrict
      | subterm base tmQ tmP = Just SCWeak
      | otherwise = Nothing

closureGraphs :: [SCGraph] -> S.Set SCGraph
closureGraphs base = go (S.fromList base)
  where
    go current =
      let composed =
            S.fromList
              [ g
              | g1 <- S.toList current
              , g2 <- S.toList current
              , scTo g1 == scFrom g2
              , Just g <- [composeGraph g1 g2]
              ]
          next = S.union current composed
       in if next == current
            then current
            else go next

composeGraph :: SCGraph -> SCGraph -> Maybe SCGraph
composeGraph g1 g2
  | scToArity g1 /= scFromArity g2 = Nothing
  | otherwise =
      Just
        SCGraph
          { scFrom = scFrom g1
          , scTo = scTo g2
          , scHidden = scHidden g1 || scHidden g2
          , scFromArity = scFromArity g1
          , scToArity = scToArity g2
          , scEdges = composeEdges
          }
  where
    composeEdges =
      M.fromList
        [ ((i, k), rel)
        | i <- [0 .. scFromArity g1 - 1]
        , k <- [0 .. scToArity g2 - 1]
        , Just rel <- [composeRelAt i k]
        ]

    composeRelAt i k =
      let rels =
            [ composeRel r1 r2
            | j <- [0 .. scToArity g1 - 1]
            , Just r1 <- [M.lookup (i, j) (scEdges g1)]
            , Just r2 <- [M.lookup (j, k) (scEdges g2)]
            ]
       in if null rels
            then Nothing
            else
              if SCStrict `elem` rels
                then Just SCStrict
                else Just SCWeak

composeRel :: SCRel -> SCRel -> SCRel
composeRel SCStrict _ = SCStrict
composeRel _ SCStrict = SCStrict
composeRel SCWeak SCWeak = SCWeak

isIdempotent :: SCGraph -> Bool
isIdempotent g =
  (not (M.null (scEdges g)) || scHidden g)
    && case composeGraph g g of
      Nothing -> False
      Just gg -> gg == g

hasStrictSelfLoop :: SCGraph -> Bool
hasStrictSelfLoop g
  | scFrom g /= scTo g = True
  | otherwise =
      any
        (\i -> M.lookup (i, i) (scEdges g) == Just SCStrict)
        [0 .. min (scFromArity g) (scToArity g) - 1]

subterm :: Int -> TermExpr -> TermExpr -> Bool
subterm binderBase needle tm
  | needle == tm = True
  | otherwise =
      case tm of
        TMHead _ args bargs ->
          any (subtermHeadArg binderBase needle) args
            || any (subtermBinderArg binderBase needle) bargs
        TMSplice _ _ args ->
          any (subterm binderBase needle) args
        TMMeta _ _ -> False
        TMBound _ -> False
        TMLit _ -> False

subtermHeadArg :: Int -> TermExpr -> TermHeadArg -> Bool
subtermHeadArg binderBase needle arg =
  case arg of
    THAObj _ -> False
    THATm tm -> subterm binderBase needle tm

subtermBinderArg :: Int -> TermExpr -> TermBinderArg -> Bool
subtermBinderArg binderBase needle barg =
  case barg of
    TBABody inner ->
      case diagramOutputTerms binderBase inner of
        Left _ -> False
        Right terms -> any (subterm binderBase needle) terms
    TBAHole _ -> False

strictSubterm :: Int -> TermExpr -> TermExpr -> Bool
strictSubterm binderBase needle tm = needle /= tm && subterm binderBase needle tm

diagramOutputTerms :: Int -> Diagram -> Either Text [TermExpr]
diagramOutputTerms binderBase diag =
  mapM (readPort S.empty) (dOut diag)
  where
    inMap = M.fromList (zip (dIn diag) [0 :: Int ..])

    readPort seen pid =
      case M.lookup pid inMap of
        Just local ->
          Right (TMBound (binderBase + local))
        Nothing ->
          if pid `S.member` seen
            then Left "termination checker: cycle detected in binder body"
            else do
              edge <- producerEdge pid
              buildEdge (S.insert pid seen) edge

    producerEdge pid =
      case IM.lookup (unPortId pid) (dProd diag) of
        Just (Just eid) ->
          case IM.lookup (unEdgeId eid) (dEdges diag) of
            Just edge -> Right edge
            Nothing -> Left "termination checker: missing producer in binder body"
        _ -> Left "termination checker: missing producer in binder body"

    buildEdge seen edge =
      case ePayload edge of
        PGen f args bargs -> do
          storedArgs <- mapM decodeCodeArg args
          inputArgs <- mapM (decodeInput seen) (eIns edge)
          binderArgs <- mapM decodeBinderArg bargs
          Right (TMHead f (storedArgs <> inputArgs) binderArgs)
        PTmMeta v -> do
          metaArgs <- mapM boundaryLocal (eIns edge)
          Right (TMMeta v metaArgs)
        PTmLit lit ->
          Right (TMLit lit)
        PProvider _ ->
          Right (opaqueEdgeTerm "provider" edge)
        PModuleRef _ ->
          Right (opaqueEdgeTerm "module_ref" edge)
        PBox _ _ ->
          Right (opaqueEdgeTerm "box" edge)
        PFeedback _ ->
          Right (opaqueEdgeTerm "feedback" edge)
        PSplice hole me -> do
          args <- mapM (readPort seen) (eIns edge)
          Right (TMSplice hole me args)
        PInternalDrop ->
          Right (opaqueEdgeTerm "drop" edge)

    decodeInput seen pid =
      THATm <$> readPort seen pid

    decodeCodeArg arg =
      case arg of
        CAObj obj -> Right (THAObj obj)
        CATm tm -> do
          expr <- termDiagramExpr tm
          Right (THATm expr)

    decodeBinderArg barg =
      case barg of
        BAConcrete inner -> Right (TBABody inner)
        BAMeta hole -> Right (TBAHole hole)

    boundaryLocal pid =
      case M.lookup pid inMap of
        Just local -> Right (binderBase + local)
        Nothing -> Left "termination checker: PTmMeta inputs in binder body must connect to boundary inputs"

    termDiagramExpr (TermDiagram inner) =
      case dOut inner of
        [_] -> do
          terms <- diagramOutputTerms binderBase inner
          case terms of
            [term] -> Right term
            _ -> Left "termination checker: stored term arguments must have exactly one output"
        _ ->
          Left "termination checker: stored term arguments must have exactly one output"

    opaqueEdgeTerm tag edge =
      TMMeta
        (mkModeMetaVar ("__sct_binder_" <> tag <> "_" <> renderEdgeId (eId edge)) (dMode diag))
        []

renderEdgeId :: EdgeId -> Text
renderEdgeId (EdgeId i) = T.pack (show i)

renderMode :: TRS -> Text
renderMode trs =
  case trsMode trs of
    -- Show instance of ModeName is stable and sufficient for diagnostics.
    m -> T.pack (show m)

renderGraphs :: [SCGraph] -> Text
renderGraphs gs
  | null gs = "(none)"
  | otherwise = T.intercalate "\n" (map renderGraph gs)

renderGraph :: SCGraph -> Text
renderGraph g =
  renderFun (scFrom g)
    <> "/"
    <> T.pack (show (scFromArity g))
    <> " -> "
    <> renderFun (scTo g)
    <> "/"
    <> T.pack (show (scToArity g))
    <> " {"
    <> T.intercalate ", " (map renderEdge (L.sort (M.toList (scEdges g))))
    <> "}"

renderEdge :: ((Int, Int), SCRel) -> Text
renderEdge ((i, j), rel) =
  T.pack (show i)
    <> symbol
    <> T.pack (show j)
  where
    symbol =
      case rel of
        SCStrict -> "-<"
        SCWeak -> "<="

renderFun :: GenName -> Text
renderFun (GenName t) = t

indent :: Text -> Text
indent t =
  T.unlines
    [ "  " <> line
    | line <- T.lines t
    ]
