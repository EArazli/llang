{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.Poly.CriticalPairs
  ( CPMode(..)
  , CriticalPair(..)
  , CriticalPairInfo(..)
  , RuleInfo(..)
  , criticalPairsForRules
  , criticalPairsForRulesInTypeTheoryWithMapper
  , criticalPairsForRulesInTypeTheory
  , nestedCriticalPairsForRulesInTypeTheoryWithMapper
  , nestedCriticalPairsForRulesInTypeTheory
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import Data.Functor.Identity (runIdentity)
import Control.Monad (foldM)
import Strat.Poly.DefEq (defEqObjWithMapper)
import Strat.Poly.Graph
import qualified Strat.Poly.DiagramIso as DiagramIso
import qualified Strat.Poly.Diagram as Diag
import Strat.Poly.Diagram
import Strat.Poly.DiagramInterpretation (requirePortType)
import Strat.Poly.Match
  ( Match(..)
  )
import Strat.Poly.ObjEq (ObjEqInCtx)
import Strat.Poly.Obj
  ( TmVar
    , tmvName
    , tmVarOwner
    , TmVar(..)
    , sameTmVarId
  , TermDiagram(..)
  , Obj(..)
  , pattern OVar
  , pattern OCon
  , pattern OMod
  , pattern OAObj
  , pattern OATm
  , mapObjExpr
  )
import qualified Strat.Poly.Subst as US
import Strat.Poly.Rewrite
  ( RewriteRule(..)
  , SpliceMapper
  , defaultSpliceMapper
  , rewriteOnceWithMapper
  , rewriteAllNested
  )
import qualified Strat.Poly.Term.SubstRuntime as SR
import qualified Strat.Poly.UnifyFlex as UF
import Strat.Poly.GenArgSigs (withStructuralZeroParamGenArgSigs)
import Strat.Common.Rules (RuleClass(..))
import Strat.Poly.ModeTheory (ModeTheory)
import Strat.Poly.ModeTheory (ModeName)
import Strat.Poly.Names (GenName)
import Strat.Poly.Syntax (CodeArg(..))
import Strat.Poly.Tele (GenParam)
import Strat.Poly.TypeTheory
  ( TypeTheory(..)
  , GenArgSig(..)
  , TmHeadSig(..)
  , BinderSig(..)
  , lookupGenArgSig
  , lookupTmHeadSig
  , modeOnlyTypeTheory
  )
import Strat.Poly.Term.HeadInst
  ( diagramBoundaryTypes
  , instantiateStoredHeadSubst
  , instantiateStructuralBinderSig
  , validateConcreteBinderDiagram
  )
import Strat.Poly.Traversal (traverseDiagram)


type Subst = US.Subst

fatalSubstPrefix :: Text
fatalSubstPrefix = "criticalPairs: substitution failure: "

fatalSubstError :: Text -> Text
fatalSubstError err = fatalSubstPrefix <> err

isFatalSubstError :: Text -> Bool
isFatalSubstError = T.isPrefixOf fatalSubstPrefix

isBenignUnifyMismatch :: Text -> Bool
isBenignUnifyMismatch err =
  "unifyTm:" `T.isPrefixOf` err
    || "unifyGenArgsFlex:" `T.isPrefixOf` err


data CPMode = CP_All | CP_OnlyStructural | CP_StructuralVsComputational
  deriving (Eq, Ord, Show)

data CriticalPair = CriticalPair
  { cpRule1   :: Text
  , cpRule2   :: Text
  , cpOverlap :: Diagram
  , cpLeft    :: Diagram
  , cpRight   :: Diagram
  } deriving (Eq, Show)

data CriticalPairInfo = CriticalPairInfo
  { cpiPair :: CriticalPair
  , cpiClass1 :: RuleClass
  , cpiClass2 :: RuleClass
  } deriving (Eq, Show)

data RuleInfo = RuleInfo
  { riLabel :: Text
  , riRule  :: RewriteRule
  , riClass :: RuleClass
  } deriving (Eq, Show)

data PartialIso = PartialIso
  { piEdgeMap :: M.Map EdgeId EdgeId
  , piPortMap :: M.Map PortId PortId
  , piUsedEdges :: S.Set EdgeId
  , piUsedPorts :: S.Set PortId
  , piTySubst :: Subst
  , piBinderSub1 :: M.Map BinderMetaVar Diagram
  , piBinderSub2 :: M.Map BinderMetaVar Diagram
  } deriving (Eq, Show)

criticalPairsForRules :: ModeTheory -> CPMode -> [RuleInfo] -> Either Text [CriticalPairInfo]
criticalPairsForRules mt mode rules =
  do
    tt <- withStructuralZeroParamGenArgSigs (concatMap ruleDiagrams rules) (modeOnlyTypeTheory mt)
    criticalPairsForRulesInTypeTheory tt mode rules

ruleDiagrams :: RuleInfo -> [Diagram]
ruleDiagrams info =
  let rule = riRule info
   in [rrLHS rule, rrRHS rule]

criticalPairsForRulesInTypeTheory :: TypeTheory -> CPMode -> [RuleInfo] -> Either Text [CriticalPairInfo]
criticalPairsForRulesInTypeTheory tt mode =
  criticalPairsForRulesInTypeTheoryWithMapper tt defaultSpliceMapper mode

criticalPairsForRulesInTypeTheoryWithMapper :: TypeTheory -> SpliceMapper -> CPMode -> [RuleInfo] -> Either Text [CriticalPairInfo]
criticalPairsForRulesInTypeTheoryWithMapper tt spliceMapper mode rules = do
  let numbered = zip [0 :: Int ..] rules
  let pairs =
        [ (r1, r2)
        | (i, r1) <- numbered
        , (j, r2) <- numbered
        , i <= j
        , allowedPairSym mode r1 r2
        ]
  pairsOut <- fmap concat (mapM (uncurry (criticalPairsForPair tt spliceMapper)) pairs)
  dedupCriticalPairs pairsOut
  where
    allowedPairSym m a b = allowedPair m a b || allowedPair m b a

nestedCriticalPairsForRulesInTypeTheory :: TypeTheory -> [RuleInfo] -> Either Text [CriticalPairInfo]
nestedCriticalPairsForRulesInTypeTheory tt =
  nestedCriticalPairsForRulesInTypeTheoryWithMapper tt defaultSpliceMapper

nestedCriticalPairsForRulesInTypeTheoryWithMapper :: TypeTheory -> SpliceMapper -> [RuleInfo] -> Either Text [CriticalPairInfo]
nestedCriticalPairsForRulesInTypeTheoryWithMapper tt spliceMapper rules = do
  let orderedPairs =
        [ (r1, r2)
        | r1 <- rules
        , r2 <- rules
        ]
  pairsOut <- fmap concat (mapM (uncurry (nestedCriticalPairsForPair tt spliceMapper)) orderedPairs)
  dedupCriticalPairs pairsOut

allowedPair :: CPMode -> RuleInfo -> RuleInfo -> Bool
allowedPair mode r1 r2 =
  case mode of
    CP_All -> True
    CP_OnlyStructural -> riClass r1 == Structural && riClass r2 == Structural
    CP_StructuralVsComputational ->
      (riClass r1 == Structural && riClass r2 == Computational)
        || (riClass r1 == Computational && riClass r2 == Structural)

criticalPairsForPair :: TypeTheory -> SpliceMapper -> RuleInfo -> RuleInfo -> Either Text [CriticalPairInfo]
criticalPairsForPair tt spliceMapper r1 r2 = do
  let r1' = renameRule 0 (riRule r1)
  let r2' = renameRule 1 (riRule r2)
  let tyFlex = S.fromList (rrTyVars r1' <> rrTyVars r2')
  let flex = S.unions [tyFlex, freeVarsDiagram (rrLHS r1'), freeVarsDiagram (rrLHS r2')]
  let objEq = defEqObjWithMapper tt spliceMapper
  overlaps <- enumerateOverlaps objEq tt flex (rrLHS r1') (rrLHS r2')
  rootPairs <- fmap concat (mapM (buildPair r1 r2 r1' r2') overlaps)
  nested12 <- buildNestedPairsForPair tt spliceMapper r1 r2 r1' r2'
  nested21 <- buildNestedPairsForPair tt spliceMapper r2 r1 r2' r1'
  pure (rootPairs <> nested12 <> nested21)
  where
    buildPair r1Info r2Info rule1 rule2 ov = do
      case do
        (host, match1, match2) <- buildOverlapHost tt (rrLHS rule1) (rrLHS rule2) ov
        if danglingOk (rrLHS rule1) host match1 && danglingOk (rrLHS rule2) host match2
          then do
            left <- applyRuleAtMatch tt rule1 match1 host
            right <- applyRuleAtMatch tt rule2 match2 host
            overlap' <- canonDiagramRaw host
            left' <- canonDiagramRaw left
            right' <- canonDiagramRaw right
            let cp = CriticalPair
                  { cpRule1 = riLabel r1Info
                  , cpRule2 = riLabel r2Info
                  , cpOverlap = overlap'
                  , cpLeft = left'
                  , cpRight = right'
                  }
            pure [CriticalPairInfo cp (riClass r1Info) (riClass r2Info)]
          else Right []
        of
          Left err
            | isFatalSubstError err -> Left err
            | otherwise -> Right []
          Right cps -> Right cps

nestedCriticalPairsForPair :: TypeTheory -> SpliceMapper -> RuleInfo -> RuleInfo -> Either Text [CriticalPairInfo]
nestedCriticalPairsForPair tt spliceMapper outerInfo innerInfo = do
  let outerRule = renameRule 0 (riRule outerInfo)
  let innerRule = renameRule 1 (riRule innerInfo)
  buildNestedPairsForPair tt spliceMapper outerInfo innerInfo outerRule innerRule

buildNestedPairsForPair
  :: TypeTheory
  -> SpliceMapper
  -> RuleInfo
  -> RuleInfo
  -> RewriteRule
  -> RewriteRule
  -> Either Text [CriticalPairInfo]
buildNestedPairsForPair tt spliceMapper outerInfo innerInfo outerRule innerRule = do
  let objEq = defEqObjWithMapper tt spliceMapper
  rewritten <- rewriteAllNested objEq tt spliceMapper maxBound [innerRule] (rrLHS outerRule)
  directPairs <- fmap concat (mapM (mkNestedPair outerInfo innerInfo outerRule) rewritten)
  binderPairs <- buildBinderHolePairs tt spliceMapper outerInfo innerInfo outerRule innerRule
  pure (directPairs <> binderPairs)
  where
    mkNestedPair outerInfo' innerInfo' outerRule' rewritten = do
      overlap' <- canonDiagramRaw (rrLHS outerRule')
      left' <- canonDiagramRaw (rrRHS outerRule')
      right' <- canonDiagramRaw rewritten
      let cp = CriticalPair
            { cpRule1 = riLabel outerInfo'
            , cpRule2 = riLabel innerInfo'
            , cpOverlap = overlap'
            , cpLeft = left'
            , cpRight = right'
            }
      pure [CriticalPairInfo cp (riClass outerInfo') (riClass innerInfo')]

buildBinderHolePairs
  :: TypeTheory
  -> SpliceMapper
  -> RuleInfo
  -> RuleInfo
  -> RewriteRule
  -> RewriteRule
  -> Either Text [CriticalPairInfo]
buildBinderHolePairs tt spliceMapper outerInfo innerInfo outerRule innerRule
  | dMode (rrLHS outerRule) /= dMode (rrLHS innerRule) =
      Right []
  | otherwise = do
      slots <- collectBinderMetaSlots tt (rrLHS outerRule)
      fmap concat $
        mapM
          (buildOneBinderHolePair tt spliceMapper outerInfo innerInfo outerRule innerRule)
          (M.toList slots)

buildOneBinderHolePair
  :: TypeTheory
  -> SpliceMapper
  -> RuleInfo
  -> RuleInfo
  -> RewriteRule
  -> RewriteRule
  -> (BinderMetaVar, BinderSig)
  -> Either Text [CriticalPairInfo]
buildOneBinderHolePair tt spliceMapper outerInfo innerInfo outerRule innerRule (meta, slot) = do
  let objEq = defEqObjWithMapper tt spliceMapper
  mInst <- instantiateRuleForBinderSlot tt slot innerRule
  case mInst of
    Nothing ->
      Right []
    Just (innerLHS, innerRHS) -> do
      overlap <- replaceBinderMetaAll meta innerLHS (rrLHS outerRule)
      rewritten <- replaceBinderMetaAll meta innerRHS (rrLHS outerRule)
      validateDiagram overlap
      validateDiagram rewritten
      case rewriteOnceWithMapper objEq tt spliceMapper [outerRule] overlap of
        Left _ ->
          Right []
        Right Nothing ->
          Right []
        Right (Just left) -> do
          overlap' <- canonDiagramRaw overlap
          left' <- canonDiagramRaw left
          right' <- canonDiagramRaw rewritten
          let cp =
                CriticalPair
                  { cpRule1 = riLabel outerInfo
                  , cpRule2 = riLabel innerInfo
                  , cpOverlap = overlap'
                  , cpLeft = left'
                  , cpRight = right'
                  }
          pure [CriticalPairInfo cp (riClass outerInfo) (riClass innerInfo)]

collectBinderMetaSlots :: TypeTheory -> Diagram -> Either Text (M.Map BinderMetaVar BinderSig)
collectBinderMetaSlots tt = go M.empty
  where
    go acc diag =
      foldM stepEdge acc (IM.elems (dEdges diag))
      where
        stepEdge acc0 edge =
          case ePayload edge of
            PGen g args bargs -> do
              acc1 <- foldM stepCodeArg acc0 args
              acc2 <- foldM stepBinderArg acc1 bargs
              if not (any isBinderMetaArg bargs)
                then Right acc2
                else do
                  sig <-
                    case lookupTmHeadSig tt (dMode diag) g of
                      Nothing -> Left "criticalPairs: missing term-head signature while collecting binder overlaps"
                      Just sig0 -> Right sig0
                  if length args /= length (thsParams sig) || length bargs /= length (thsBinders sig)
                    then Left "criticalPairs: term-head arity mismatch while collecting binder overlaps"
                    else do
                      headSubst <- instantiateStoredHeadSubst tt (dTmCtx diag) sig args
                      slots <- mapM (instantiateStructuralBinderSig tt (dTmCtx diag) headSubst) (thsBinders sig)
                      foldM insertSite acc2 (zip bargs slots)
            PBox _ inner ->
              go acc0 inner
            PFeedback inner ->
              go acc0 inner
            _ ->
              Right acc0

        isBinderMetaArg barg =
          case barg of
            BAMeta _ -> True
            BAConcrete _ -> False

        stepCodeArg acc0 arg =
          case arg of
            CAObj _ -> Right acc0
            CATm (TermDiagram inner) -> go acc0 inner

        stepBinderArg acc0 barg =
          case barg of
            BAConcrete inner -> go acc0 inner
            BAMeta _ -> Right acc0

        insertSite acc0 (barg, slot) =
          case barg of
            BAMeta x ->
              case M.lookup x acc0 of
                Nothing -> Right (M.insert x slot acc0)
                Just slot0
                  | slot0 == slot -> Right acc0
                  | otherwise ->
                      Left "criticalPairs: binder metavariable is used at incompatible binder slots"
            BAConcrete _ ->
              Right acc0

instantiateRuleForBinderSlot
  :: TypeTheory
  -> BinderSig
  -> RewriteRule
  -> Either Text (Maybe (Diagram, Diagram))
instantiateRuleForBinderSlot tt slot rule = do
  let lhs0 = rrLHS rule
      rhs0 = rrRHS rule
      flex = S.fromList (rrTyVars rule <> rrTmVars rule)
      binderTmCtx = bsTmCtx slot

  let tryCompat action =
        case action of
          Left _ -> Nothing
          Right x -> Just x

      unifyBoundary subst lhsBoundary slotBoundary
        | length lhsBoundary /= length slotBoundary = Left "criticalPairs: binder boundary length mismatch"
        | otherwise =
            foldM
              (\substAcc (lhsTy, slotTy) -> UF.unifyObjFlex tt binderTmCtx flex substAcc lhsTy slotTy)
              subst
              (zip lhsBoundary slotBoundary)

  lhsDom <- diagramBoundaryTypes lhs0 (dIn lhs0)
  lhsCod <- diagramBoundaryTypes lhs0 (dOut lhs0)
  case tryCompat (UF.unifyCtx tt binderTmCtx flex (dTmCtx lhs0) binderTmCtx) of
    Nothing ->
      Right Nothing
    Just subst0 ->
      case tryCompat (unifyBoundary subst0 lhsDom (bsDom slot)) of
        Nothing ->
          Right Nothing
        Just subst1 ->
          case tryCompat (unifyBoundary subst1 lhsCod (bsCod slot)) of
            Nothing ->
              Right Nothing
            Just subst2 -> do
              subst <- SR.normalizeSubst tt subst2
              lhs' <- SR.applySubstDiagram tt subst lhs0
              rhs' <- SR.applySubstDiagram tt subst rhs0
              case (validateConcreteBinderDiagram slot lhs', validateConcreteBinderDiagram slot rhs') of
                (Right (), Right ()) ->
                  Right (Just (lhs', rhs'))
                _ ->
                  Right Nothing

replaceBinderMetaAll :: BinderMetaVar -> Diagram -> Diagram -> Either Text Diagram
replaceBinderMetaAll meta replacement =
  traverseDiagram pure pure pure onBinder
  where
    onBinder barg =
      pure $
        case barg of
          BAMeta x
            | x == meta -> BAConcrete replacement
          _ -> barg

renameRule :: Int -> RewriteRule -> RewriteRule
renameRule idx rule =
  let idxText = T.pack (show idx)
      tySuffix = ":" <> idxText
      tmSuffix = "$" <> idxText
      binderSuffix = "%" <> idxText
      renamedTyVars = M.fromList [ (v, renameTyVar v) | v <- rrTyVars rule ]
      renameTyVar v = v { tmvName = tmvName v <> tySuffix }
      renameBinderMeta (BinderMetaVar name) = BinderMetaVar (name <> binderSuffix)
      renameTyNode ty =
        case ty of
          OVar v ->
            case M.lookup v renamedTyVars of
              Just v' -> OVar v'
              Nothing -> OVar v
          _ -> ty
      renameTmVar v =
        v
          { tmvName = tmvName v <> tmSuffix
          , tmvSort = renameTmType (tmvSort v)
          }
      renameTmTerm (TermDiagram diag) =
        TermDiagram $
          runIdentity $
            traverseDiagram onDiag onPayload onCodeArg pure diag
        where
          onDiag d =
            pure d
              { dPortObj = IM.map renameTmType (dPortObj d)
              , dTmCtx = map renameTmType (dTmCtx d)
              }
          onCodeArg arg =
            pure $
              case arg of
                CAObj obj -> CAObj (renameTmType obj)
                CATm tmArg -> CATm tmArg
      onPayload payload =
        pure $
          case payload of
            PTmMeta v -> PTmMeta (renameTmVar v)
            _ -> payload
      renameTmType ty = mapObjExpr renameTyNode renameTmTerm ty
      lhsTm' = renameTmVarsDiagram renameTmType (rrLHS rule)
      rhsTm' = renameTmVarsDiagram renameTmType (rrRHS rule)
      lhsB' = renameBinderMetasDiagram renameBinderMeta lhsTm'
      rhsB' = renameBinderMetasDiagram renameBinderMeta rhsTm'
      lhs' = lhsB'
      rhs' = rhsB'
      tyvars' = map renameTyVar (rrTyVars rule)
      tmVars' = map renameTmVar (rrTmVars rule)
  in rule { rrLHS = lhs', rrRHS = rhs', rrTyVars = tyvars', rrTmVars = tmVars' }

enumerateOverlaps :: ObjEqInCtx -> TypeTheory -> S.Set TmVar -> Diagram -> Diagram -> Either Text [PartialIso]
enumerateOverlaps objEq tt flex l1 l2 =
  if dMode l1 /= dMode l2 || dTmCtx l1 /= dTmCtx l2
    then Right []
    else do
      let edges1 = sortEdges (IM.elems (dEdges l1))
      let edges2 = sortEdges (IM.elems (dEdges l2))
      fmap concat (mapM (seedFrom edges2) edges1)
  where
    emptyState = PartialIso M.empty M.empty S.empty S.empty US.emptySubst M.empty M.empty
    seedFrom edges2 e1 =
      fmap concat (mapM (expandFromSeed e1) edges2)
    expandFromSeed e1 e2 = do
      seeds <- mapEdge objEq tt flex l1 l2 emptyState e1 e2
      fmap concat (mapM (expandState objEq tt l1 l2 flex) seeds)

expandState :: ObjEqInCtx -> TypeTheory -> Diagram -> Diagram -> S.Set TmVar -> PartialIso -> Either Text [PartialIso]
expandState objEq tt l1 l2 flex st = do
  let mappedPorts = S.fromList (M.keys (piPortMap st))
  let candidates =
        [ e
        | e <- sortEdges (IM.elems (dEdges l1))
        , M.notMember (eId e) (piEdgeMap st)
        , any (`S.member` mappedPorts) (eIns e <> eOuts e)
        ]
  expanded <- fmap concat (mapM (expandEdge objEq tt l1 l2 flex st) candidates)
  deeper <- fmap concat (mapM (expandState objEq tt l1 l2 flex) expanded)
  pure (st : deeper)

expandEdge :: ObjEqInCtx -> TypeTheory -> Diagram -> Diagram -> S.Set TmVar -> PartialIso -> Edge -> Either Text [PartialIso]
expandEdge objEq tt l1 l2 flex st e1 = do
  let candidates =
        [ e2
        | e2 <- sortEdges (IM.elems (dEdges l2))
        , eId e2 `S.notMember` piUsedEdges st
        , edgeCompatible e1 e2
        ]
  fmap concat (mapM (mapEdge objEq tt flex l1 l2 st e1) candidates)

mapEdge :: ObjEqInCtx -> TypeTheory -> S.Set TmVar -> Diagram -> Diagram -> PartialIso -> Edge -> Edge -> Either Text [PartialIso]
mapEdge objEq tt flex l1 l2 st e1 e2 =
  if M.member (eId e1) (piEdgeMap st)
    then Right []
    else if eId e2 `S.member` piUsedEdges st
    then Right []
    else if length (eIns e1) /= length (eIns e2) || length (eOuts e1) /= length (eOuts e2)
      then Right []
      else do
        substs <-
          payloadSubsts
            objEq
            tt
            flex
            l1
            (piTySubst st)
            (piBinderSub1 st)
            (piBinderSub2 st)
            (ePayload e1)
            (ePayload e2)
        fmap concat (mapM extendPorts substs)
  where
    extendPorts (tySubst0, binderSub1, binderSub2) = do
      let pairs = zip (eIns e1) (eIns e2) <> zip (eOuts e1) (eOuts e2)
      case foldl (extendPort tt l1 l2 flex) (Right (piPortMap st, piUsedPorts st, tySubst0)) pairs of
        Left err ->
          if isFatalSubstError err
            then Left err
            else Right []
        Right (portMap', usedPorts', tySubst') -> do
          let edgeMap' = M.insert (eId e1) (eId e2) (piEdgeMap st)
          let usedEdges' = S.insert (eId e2) (piUsedEdges st)
          pure
            [ st
                { piEdgeMap = edgeMap'
                , piPortMap = portMap'
                , piUsedEdges = usedEdges'
                , piUsedPorts = usedPorts'
                , piTySubst = tySubst'
                , piBinderSub1 = binderSub1
                , piBinderSub2 = binderSub2
                }
            ]

extendPort :: TypeTheory -> Diagram -> Diagram -> S.Set TmVar -> Either Text (M.Map PortId PortId, S.Set PortId, Subst) -> (PortId, PortId) -> Either Text (M.Map PortId PortId, S.Set PortId, Subst)
extendPort tt l1 l2 flex acc (p1, p2) = do
  (portMap, usedPorts, tySubst) <- acc
  case M.lookup p1 portMap of
    Just p2' ->
      if p2' == p2 then Right (portMap, usedPorts, tySubst) else Left "criticalPairs: port mapping conflict"
    Nothing ->
      if p2 `S.member` usedPorts
        then Left "criticalPairs: target port already used"
        else do
          s1 <- unifyPorts tt l1 l2 flex tySubst p1 p2
          tySubst' <- mapLeft fatalSubstError (SR.composeSubst tt s1 tySubst)
          Right (M.insert p1 p2 portMap, S.insert p2 usedPorts, tySubst')

unifyPorts :: TypeTheory -> Diagram -> Diagram -> S.Set TmVar -> Subst -> PortId -> PortId -> Either Text Subst
unifyPorts tt l1 l2 flex subst p1 p2 = do
  pTy <- requirePortType "criticalPairs" l1 p1
  hTy <- requirePortType "criticalPairs" l2 p2
  pTy' <- mapLeft fatalSubstError (SR.applySubstObj tt subst pTy)
  hTy' <- mapLeft fatalSubstError (SR.applySubstObj tt subst hTy)
  tmCtx' <- mapLeft fatalSubstError (SR.applySubstCtx tt subst (dTmCtx l1))
  UF.unifyObjFlex
    tt
    tmCtx'
    flex
    US.emptySubst
    pTy'
    hTy'

payloadSubsts
  :: ObjEqInCtx
  -> TypeTheory
  -> S.Set TmVar
  -> Diagram
  -> Subst
  -> M.Map BinderMetaVar Diagram
  -> M.Map BinderMetaVar Diagram
  -> EdgePayload
  -> EdgePayload
  -> Either Text [(Subst, M.Map BinderMetaVar Diagram, M.Map BinderMetaVar Diagram)]
payloadSubsts objEq tt flex lhs tySubst binderSub1 binderSub2 p1 p2 =
  case (p1, p2) of
    (PGen g1 args1 bargs1, PGen g2 args2 bargs2) ->
      if g1 /= g2 || length args1 /= length args2 || length bargs1 /= length bargs2
        then Right []
        else do
          tmCtx' <- mapLeft fatalSubstError (SR.applySubstCtx tt tySubst (dTmCtx lhs))
          case lookupGenArgParams tt (dMode lhs) g1 args1 args2 of
            Nothing -> Right []
            Just params ->
              case UF.unifyGenArgsFlex tt tmCtx' flex tySubst params args1 args2 of
                Left err
                  | isBenignUnifyMismatch err -> Right []
                  | otherwise -> mapLeft fatalSubstError (Left err)
                Right tySubst' ->
                  foldl step (Right [(tySubst', binderSub1, binderSub2)]) (zip bargs1 bargs2)
      where
        step acc pair = do
          subs <- acc
          fmap concat (mapM (\(tyS, sub1, sub2) -> binderArgSubsts tyS sub1 sub2 pair) subs)

        binderArgSubsts tySubst0 binderSub1' binderSub2' (lhsArg, rhsArg) =
          case (lhsArg, rhsArg) of
            (BAConcrete d1, BAConcrete d2) -> do
              substs <-
                mapLeft
                  fatalSubstError
                  (DiagramIso.diagramIsoMatchWithVarsFrom objEq tt flex tySubst0 d1 d2)
              pure [ (tyS, binderSub1', binderSub2') | tyS <- substs ]
            (BAMeta x, BAConcrete d2) -> do
              captures <- extendBinderCapture objEq tt flex tySubst0 binderSub1' x d2
              pure [ (tyS, sub1', binderSub2') | (tyS, sub1') <- captures ]
            (BAConcrete d1, BAMeta y) -> do
              captures <- extendBinderCapture objEq tt flex tySubst0 binderSub2' y d1
              pure [ (tyS, binderSub1', sub2') | (tyS, sub2') <- captures ]
            (BAMeta x, BAMeta y) ->
              if x == y
                then Right [(tySubst0, binderSub1', binderSub2')]
                else Right []
            _ -> Right []
    (PProvider ref1, PProvider ref2)
      | ref1 == ref2 -> Right [(tySubst, binderSub1, binderSub2)]
    (PModuleRef ref1, PModuleRef ref2)
      | ref1 == ref2 -> Right [(tySubst, binderSub1, binderSub2)]
    (PBox _ d1, PBox _ d2) -> do
      substs <-
        mapLeft
          fatalSubstError
          (DiagramIso.diagramIsoMatchWithVarsFrom objEq tt flex tySubst d1 d2)
      pure [ (tyS, binderSub1, binderSub2) | tyS <- substs ]
    (PFeedback d1, PFeedback d2) ->
      do
        substs <-
          mapLeft
            fatalSubstError
            (DiagramIso.diagramIsoMatchWithVarsFrom objEq tt flex tySubst d1 d2)
        pure [ (tyS, binderSub1, binderSub2) | tyS <- substs ]
    (PSplice x me1, PSplice y me2)
      | x == y && me1 == me2 -> Right [(tySubst, binderSub1, binderSub2)]
    (PTmMeta x, PTmMeta y)
      | sameTmVarId x y -> Right [(tySubst, binderSub1, binderSub2)]
    (PTmLit x, PTmLit y)
      | x == y -> Right [(tySubst, binderSub1, binderSub2)]
    (PInternalDrop, PInternalDrop) -> Right [(tySubst, binderSub1, binderSub2)]
    _ -> Right []

extendBinderCapture
  :: ObjEqInCtx
  -> TypeTheory
  -> S.Set TmVar
  -> Subst
  -> M.Map BinderMetaVar Diagram
  -> BinderMetaVar
  -> Diagram
  -> Either Text [(Subst, M.Map BinderMetaVar Diagram)]
extendBinderCapture objEq tt flex tySubst binderSub meta captured =
  case M.lookup meta binderSub of
    Nothing ->
      Right [(tySubst, M.insert meta captured binderSub)]
    Just existing -> do
      substs <-
        mapLeft
          fatalSubstError
          (DiagramIso.diagramIsoMatchWithVarsFrom objEq tt flex tySubst existing captured)
      pure [ (tyS, binderSub) | tyS <- substs ]

lookupGenArgParams :: TypeTheory -> ModeName -> GenName -> [CodeArg] -> [CodeArg] -> Maybe [GenParam]
lookupGenArgParams tt mode g _args1 _args2 =
  case lookupGenArgSig tt mode g of
    Just sig -> Just (gasParams sig)
    Nothing -> Nothing

edgeCompatible :: Edge -> Edge -> Bool
edgeCompatible e1 e2 =
  length (eIns e1) == length (eIns e2)
    && length (eOuts e1) == length (eOuts e2)
    && payloadCompatible (ePayload e1) (ePayload e2)

payloadCompatible :: EdgePayload -> EdgePayload -> Bool
payloadCompatible p1 p2 =
  case (p1, p2) of
    (PGen g1 args1 bargs1, PGen g2 args2 bargs2) ->
      g1 == g2
        && length args1 == length args2
        && and (zipWith sameArgKind args1 args2)
        && length bargs1 == length bargs2
    (PProvider ref1, PProvider ref2) -> ref1 == ref2
    (PModuleRef ref1, PModuleRef ref2) -> ref1 == ref2
    (PBox _ _, PBox _ _) -> True
    (PFeedback _, PFeedback _) -> True
    (PSplice x me1, PSplice y me2) -> x == y && me1 == me2
    (PTmMeta x, PTmMeta y) -> sameTmVarId x y
    (PTmLit x, PTmLit y) -> x == y
    (PInternalDrop, PInternalDrop) -> True
    _ -> False
  where
    sameArgKind (CAObj _) (CAObj _) = True
    sameArgKind (CATm _) (CATm _) = True
    sameArgKind _ _ = False

sortEdges :: [Edge] -> [Edge]
sortEdges = L.sortOn (unEdgeId . eId)

buildOverlapHost :: TypeTheory -> Diagram -> Diagram -> PartialIso -> Either Text (Diagram, Match, Match)
buildOverlapHost tt l1 l2 ov = do
  let tySubst = piTySubst ov
  (binderSub1, binderSub2) <-
    resolveOverlapBinderSubs tt tySubst (piBinderSub1 ov) (piBinderSub2 ov)
  l1Ty <- applySubstsDiagramLocal tt tySubst l1
  l2Ty <- applySubstsDiagramLocal tt tySubst l2
  l1' <- instantiateBinderMetasLocal binderSub1 l1Ty
  l2' <- instantiateBinderMetasLocal binderSub2 l2Ty
  let portMapL2 = M.fromList [ (p2, p1) | (p1, p2) <- M.toList (piPortMap ov) ]
  let edgeMapL2 = M.fromList [ (e2, e1) | (e1, e2) <- M.toList (piEdgeMap ov) ]
  (host1, portMap1, edgeMap1) <- insertEdgesFromL2 l1' l2' portMapL2 edgeMapL2
  (host2, portMap2) <- mapBoundaryPorts host1 l2' portMap1
  let host3 =
        host2
          { dIn = dedupePorts (dIn l1' <> mapPorts portMap2 (dIn l2'))
          , dOut = dedupePorts (dOut l1' <> mapPorts portMap2 (dOut l2'))
          }
  validateDiagram host3
  let m1 = mkIdentityMatch tySubst binderSub1 l1'
  let m2 = mkMatchForL2 tySubst binderSub2 l2' portMap2 edgeMap1
  pure (host3, m1, m2)

resolveOverlapBinderSubs
  :: TypeTheory
  -> Subst
  -> M.Map BinderMetaVar Diagram
  -> M.Map BinderMetaVar Diagram
  -> Either Text (M.Map BinderMetaVar Diagram, M.Map BinderMetaVar Diagram)
resolveOverlapBinderSubs tt tySubst binderSub1 binderSub2 = do
  binderSub1Ty <- mapM (applySubstsDiagramLocal tt tySubst) binderSub1
  binderSub2Ty <- mapM (applySubstsDiagramLocal tt tySubst) binderSub2
  let allSubs = M.union binderSub1Ty binderSub2Ty
      leftKeys = S.fromList (M.keys binderSub1Ty)
      rightKeys = S.fromList (M.keys binderSub2Ty)
  resolved <- mapM (resolveCaptured allSubs S.empty) allSubs
  pure
    ( M.filterWithKey (\k _ -> k `S.member` leftKeys) resolved
    , M.filterWithKey (\k _ -> k `S.member` rightKeys) resolved
    )
  where
    resolveCaptured allSubs seen diag =
      traverseDiagram pure pure pure onBinder diag
      where
        onBinder barg =
          case barg of
            BAConcrete inner ->
              pure (BAConcrete inner)
            BAMeta x ->
              case M.lookup x allSubs of
                Nothing -> pure (BAMeta x)
                Just captured
                  | x `S.member` seen ->
                      Left "criticalPairs: binder substitution cycle while building overlap host"
                  | otherwise ->
                      BAConcrete <$> resolveCaptured allSubs (S.insert x seen) captured

instantiateBinderMetasLocal :: M.Map BinderMetaVar Diagram -> Diagram -> Either Text Diagram
instantiateBinderMetasLocal binderSub =
  traverseDiagram pure pure pure onBinderArg
  where
    onBinderArg barg =
      pure $
        case barg of
          BAConcrete inner -> BAConcrete inner
          BAMeta x ->
            case M.lookup x binderSub of
              Nothing -> BAMeta x
              Just captured -> BAConcrete captured

insertEdgesFromL2 :: Diagram -> Diagram -> M.Map PortId PortId -> M.Map EdgeId EdgeId -> Either Text (Diagram, M.Map PortId PortId, M.Map EdgeId EdgeId)
insertEdgesFromL2 host l2 portMap edgeMap =
  foldl step (Right (host, portMap, edgeMap)) (sortEdges (IM.elems (dEdges l2)))
  where
    step acc edge =
      case acc of
        Left err -> Left err
        Right (h, pm, em) ->
          case M.lookup (eId edge) em of
            Just _ -> Right (h, pm, em)
            Nothing -> do
              (h1, pm1, insHost) <- mapPortsInto h l2 pm (eIns edge)
              (h2, pm2, outsHost) <- mapPortsInto h1 l2 pm1 (eOuts edge)
              let newEdgeId = EdgeId (dNextEdge h2)
              h3 <- addEdgePayload (ePayload edge) insHost outsHost h2
              let em' = M.insert (eId edge) newEdgeId em
              Right (h3, pm2, em')

mapPortsInto :: Diagram -> Diagram -> M.Map PortId PortId -> [PortId] -> Either Text (Diagram, M.Map PortId PortId, [PortId])
mapPortsInto host l2 portMap ports =
  foldl step (Right (host, portMap, [])) ports
  where
    step acc p =
      case acc of
        Left err -> Left err
        Right (h, pm, accPorts) ->
          case M.lookup p pm of
            Just hp -> Right (h, pm, accPorts <> [hp])
            Nothing -> do
              ty <- requirePortType "criticalPairs" l2 p
              let (hp, h') = freshPort ty h
              Right (h', M.insert p hp pm, accPorts <> [hp])

mapBoundaryPorts :: Diagram -> Diagram -> M.Map PortId PortId -> Either Text (Diagram, M.Map PortId PortId)
mapBoundaryPorts host l2 portMap =
  foldl step (Right (host, portMap)) (dIn l2 <> dOut l2)
  where
    step acc p =
      case acc of
        Left err -> Left err
        Right (h, pm) ->
          case M.lookup p pm of
            Just _ -> Right (h, pm)
            Nothing -> do
              ty <- requirePortType "criticalPairs" l2 p
              let (hp, h') = freshPort ty h
              Right (h', M.insert p hp pm)

mapPorts :: M.Map PortId PortId -> [PortId] -> [PortId]
mapPorts mp = map (\p -> M.findWithDefault p p mp)

dedupePorts :: [PortId] -> [PortId]
dedupePorts = go S.empty
  where
    go _ [] = []
    go seen (p:ps)
      | p `S.member` seen = go seen ps
      | otherwise = p : go (S.insert p seen) ps

mkIdentityMatch :: Subst -> M.Map BinderMetaVar Diagram -> Diagram -> Match
mkIdentityMatch tySubst binderSub diag =
  let ports = diagramPortIds diag
      edges = IM.elems (dEdges diag)
      mPorts = M.fromList [ (p, p) | p <- ports ]
      mEdges = M.fromList [ (eId e, eId e) | e <- edges ]
      usedPorts = S.fromList ports
      usedEdges = S.fromList (map eId edges)
  in
    Match
      { mPortMap = mPorts
      , mEdgeMap = mEdges
      , mTySubst = tySubst
      , mBinderSub = binderSub
      , mUsedHostPorts = usedPorts
      , mUsedHostEdges = usedEdges
      }

mkMatchForL2 :: Subst -> M.Map BinderMetaVar Diagram -> Diagram -> M.Map PortId PortId -> M.Map EdgeId EdgeId -> Match
mkMatchForL2 tySubst binderSub l2 portMap edgeMap =
  let ports = diagramPortIds l2
      edges = IM.elems (dEdges l2)
      mPorts = M.fromList [ (p, M.findWithDefault p p portMap) | p <- ports ]
      mEdges = M.fromList [ (eId e, M.findWithDefault (eId e) (eId e) edgeMap) | e <- edges ]
      usedPorts = S.fromList (M.elems mPorts)
      usedEdges = S.fromList (M.elems mEdges)
  in
    Match
      { mPortMap = mPorts
      , mEdgeMap = mEdges
      , mTySubst = tySubst
      , mBinderSub = binderSub
      , mUsedHostPorts = usedPorts
      , mUsedHostEdges = usedEdges
      }

danglingOk :: Diagram -> Diagram -> Match -> Bool
danglingOk lhs host match =
  all okPort internalPorts
  where
    boundary = S.fromList (dIn lhs <> dOut lhs)
    allPorts = S.fromList (diagramPortIds lhs)
    internalPorts = S.toList (S.difference allPorts boundary)
    hostBoundary = S.fromList (dIn host <> dOut host)
    okPort p =
      case M.lookup p (mPortMap match) of
        Nothing -> False
        Just pHost ->
          if pHost `S.member` hostBoundary
            then False
            else
              let prod = IM.lookup (portKey pHost) (dProd host)
                  cons = IM.lookup (portKey pHost) (dCons host)
                  matchedEdges = S.fromList (M.elems (mEdgeMap match))
              in okEdge prod matchedEdges && okEdge cons matchedEdges
    okEdge entry matched =
      case entry of
        Just (Just eid) -> eid `S.member` matched
        Just Nothing -> True
        Nothing -> False
    portKey = unPortId

applyRuleAtMatch :: TypeTheory -> RewriteRule -> Match -> Diagram -> Either Text Diagram
applyRuleAtMatch tt rule match host = do
  let lhs = rrLHS rule
  rhs <- applySubstsDiagramLocal tt (mTySubst match) (rrRHS rule)
  host1 <- deleteMatchedEdges host (M.elems (mEdgeMap match))
  host2 <- deleteMatchedPorts host1 (internalPorts lhs) (mPortMap match)
  let rhsShift = shiftDiagram (dNextPort host2) (dNextEdge host2) rhs
  host3 <- unionDiagram host2 rhsShift
  let lhsBoundary = dIn lhs <> dOut lhs
  let rhsBoundary = dIn rhsShift <> dOut rhsShift
  if length lhsBoundary /= length rhsBoundary
    then Left "criticalPairs: boundary length mismatch"
    else do
      boundaryPairs <- mapM toBoundaryPair (zip lhsBoundary rhsBoundary)
      host4 <- mergeBoundaryPairs host3 boundaryPairs
      validateDiagram host4
      pure host4
  where
    toBoundaryPair (lhsPort, rhsPort) =
      case M.lookup lhsPort (mPortMap match) of
        Nothing -> Left "criticalPairs: missing boundary port mapping"
        Just hostPort -> Right (hostPort, rhsPort)

internalPorts :: Diagram -> [PortId]
internalPorts diag =
  let allPorts = S.fromList (diagramPortIds diag)
      boundary = S.fromList (dIn diag <> dOut diag)
  in S.toList (S.difference allPorts boundary)

deleteMatchedEdges :: Diagram -> [EdgeId] -> Either Text Diagram
deleteMatchedEdges diag edgeIds = foldl step (Right diag) edgeIds
  where
    step acc eid = do
      d <- acc
      deleteEdgeKeepPorts d eid

deleteMatchedPorts :: Diagram -> [PortId] -> M.Map PortId PortId -> Either Text Diagram
deleteMatchedPorts diag ports portMap = foldl step (Right diag) ports
  where
    step acc p = do
      d <- acc
      case M.lookup p portMap of
        Nothing -> Left "criticalPairs: missing port mapping"
        Just hostPort -> deletePortIfDangling d hostPort

applySubstsDiagramLocal :: TypeTheory -> Subst -> Diagram -> Either Text Diagram
applySubstsDiagramLocal tt tySubst diag =
  mapLeft fatalSubstError (Diag.applySubstDiagram tt tySubst diag)

renameTmVarsDiagram :: (Obj -> Obj) -> Diagram -> Diagram
renameTmVarsDiagram renameTy =
  runIdentity . traverseDiagram onDiag onPayload onCodeArg pure
  where
    onDiag d =
      pure d
        { dPortObj = IM.map renameTy (dPortObj d)
        , dTmCtx = map renameTy (dTmCtx d)
        }
    onPayload payload =
      pure $
        case payload of
          PTmMeta v -> PTmMeta v { tmvSort = renameTy (tmvSort v) }
          _ -> payload
    onCodeArg arg =
      pure $
        case arg of
          CAObj obj -> CAObj (renameTy obj)
          CATm tm -> CATm tm

renameBinderMetasDiagram :: (BinderMetaVar -> BinderMetaVar) -> Diagram -> Diagram
renameBinderMetasDiagram renameMeta =
  runIdentity . traverseDiagram pure onPayload pure onBArg
  where
    onPayload payload =
      pure $
        case payload of
          PSplice x me -> PSplice (renameMeta x) me
          _ -> payload

    onBArg barg =
      pure $
        case barg of
          BAMeta x -> BAMeta (renameMeta x)
          _ -> barg

dedupCriticalPairs :: [CriticalPairInfo] -> Either Text [CriticalPairInfo]
dedupCriticalPairs pairs = go [] pairs
  where
    go acc [] = Right acc
    go acc (p:ps) = do
      dup <- anyIso p acc
      if dup
        then go acc ps
        else go (acc <> [p]) ps

    anyIso _ [] = Right False
    anyIso p (x:xs) = do
      ok <- isoTriple (cpiPair p) (cpiPair x)
      if ok then Right True else anyIso p xs

    isoTriple a b = do
      okOverlap <- isoEqOrFalse (cpOverlap a) (cpOverlap b)
      if not okOverlap
        then Right False
        else do
          okDirect <- do
            okLeft <- isoEqOrFalse (cpLeft a) (cpLeft b)
            if okLeft then isoEqOrFalse (cpRight a) (cpRight b) else Right False
          if okDirect
            then Right True
            else do
              okSwap <- isoEqOrFalse (cpLeft a) (cpRight b)
              if okSwap then isoEqOrFalse (cpRight a) (cpLeft b) else Right False

    isoEqOrFalse x y =
      case DiagramIso.diagramIsoEq x y of
        Left _ -> Right False
        Right ok -> Right ok

mapLeft :: (e -> e') -> Either e a -> Either e' a
mapLeft f res =
  case res of
    Left err -> Left (f err)
    Right x -> Right x
