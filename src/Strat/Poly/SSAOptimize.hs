{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Strat.Poly.SSAOptimize
  ( SSAOptimizePolicy(..)
  , defaultSSAOptimizePolicy
  , optimizeSSA
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Attr (AttrMap)
import Strat.Poly.Doctrine
  ( Doctrine(..)
  , GenDecl(..)
  , InputShape(..)
  , gdTyVars
  )
import Strat.Poly.Foliation (SSA(..), SSAStep(..))
import Strat.Poly.Graph (PortId)
import Strat.Poly.Kernel (ObjRef, pattern OAObj, pattern OCon, pattern OVar)
import Strat.Poly.ModeTheory (cdComp, compCtxExt, compReindex, compVar, mtClassifiedBy)
import Strat.Poly.Names (GenName)


data SSAOptimizePolicy = SSAOptimizePolicy
  { sopAllowSharing :: Bool
  , sopAllowDropping :: Bool
  }
  deriving (Eq, Show)


defaultSSAOptimizePolicy :: SSAOptimizePolicy
defaultSSAOptimizePolicy =
  SSAOptimizePolicy
    { sopAllowSharing = True
    , sopAllowDropping = True
    }


optimizeSSA :: SSAOptimizePolicy -> Doctrine -> SSA -> SSA
optimizeSSA policy doc = go
  where
    go ssa =
      let info = buildOptimizeInfo policy doc ssa
          optimizedBinders = map optimizeStepBinders (ssaSteps ssa)
          st = foldl' (optimizeStep info) emptyState optimizedBinders
          outputs' = map (resolveAlias (osAliases st)) (ssaOutputs ssa)
          steps' =
            if sopAllowDropping policy
              then dceSteps info outputs' (reverse (osStepsRev st))
              else reverse (osStepsRev st)
          usedPorts = collectUsedPorts (ssaInputs ssa) outputs' steps'
          names' =
            filterPortNames usedPorts
              (promoteOutputNames usedPorts (ssaInputs ssa) (ssaOutputs ssa) outputs' (ssaPortNames ssa))
       in ssa
            { ssaSteps = steps'
            , ssaOutputs = outputs'
            , ssaPortNames = names'
            }
      where
        optimizeStepBinders step =
          case step of
            StepGen{} ->
              step
                { stepBinders = map go (stepBinders step)
                }
            StepBox{} ->
              step
                { stepInner = go (stepInner step)
                }
            StepFeedback{} ->
              step
                { stepBody = go (stepBody step)
                }

    optimizeStep info st step =
      case step of
        StepGen{} ->
          let ins' = map (resolveAlias (osAliases st)) (stepIns step)
              step' = step { stepIns = ins' }
              gen = stepGen step
              outs = stepOuts step
              binders = stepBinders step
           in case () of
                _
                  | null binders
                  , [out] <- outs
                  , [inp] <- ins'
                  , gen `S.member` oiAliasUnaryGens info ->
                      addAlias out inp st
                  | null binders
                  , [o1, o2] <- outs
                  , [inp] <- ins'
                  , sopAllowSharing policy
                  , gen `S.member` oiDupGens info ->
                      addAlias o2 inp (addAlias o1 inp st)
                  | null binders
                  , [out] <- outs
                  , [inp] <- ins'
                  , Just proj <- M.lookup gen (oiPairProjGens info) ->
                      case M.lookup inp (osPairs st) of
                        Just (lhs, rhs) ->
                          addAlias out (if proj == ProjFirst then lhs else rhs) st
                        Nothing ->
                          maybeKeepOrReuse info step' st
                  | null binders
                  , [out] <- outs
                  , [lhs, rhs] <- ins'
                  , gen `S.member` oiPairIntroGens info ->
                      case maybeReuse info step' st of
                        Just st' ->
                          st'
                        Nothing ->
                          let st' = keepStep info step' st
                           in st' { osPairs = M.insert out (lhs, rhs) (osPairs st') }
                  | otherwise ->
                      maybeKeepOrReuse info step' st
        StepBox{} ->
          keepStep
            info
            step
              { stepIns = map (resolveAlias (osAliases st)) (stepIns step)
              }
            st
        StepFeedback{} ->
          keepStep
            info
            step
              { stepIns = map (resolveAlias (osAliases st)) (stepIns step)
              }
            st
      where
        maybeKeepOrReuse info' step'' st' =
          case maybeReuse info' step'' st' of
            Just reused -> reused
            Nothing -> keepStep info' step'' st'

    maybeReuse info step st
      | not (sopAllowSharing (oiPolicy info)) = Nothing
      | otherwise =
          case cseKey info step of
            Nothing -> Nothing
            Just key ->
              case M.lookup key (osCSE st) of
                Just prevOuts
                  | length prevOuts == length (stepOuts step) ->
                      Just (foldl' (\acc (out, prevOut) -> addAlias out prevOut acc) st (zip (stepOuts step) prevOuts))
                _ ->
                  Nothing


data PairProj
  = ProjFirst
  | ProjSecond
  deriving (Eq, Ord, Show)


data OptimizeInfo = OptimizeInfo
  { oiPolicy :: SSAOptimizePolicy
  , oiAliasUnaryGens :: S.Set GenName
  , oiDupGens :: S.Set GenName
  , oiPairIntroGens :: S.Set GenName
  , oiPairProjGens :: M.Map GenName PairProj
  , oiReusableGens :: S.Set GenName
  , oiSafeDropGens :: S.Set GenName
  }


data OptState = OptState
  { osAliases :: M.Map PortId PortId
  , osPairs :: M.Map PortId (PortId, PortId)
  , osCSE :: M.Map CSEKey [PortId]
  , osStepsRev :: [SSAStep]
  }


data CSEKey = CSEKey
  { ckGen :: GenName
  , ckAttrs :: AttrMap
  , ckIns :: [PortId]
  }
  deriving (Eq, Ord, Show)


emptyState :: OptState
emptyState =
  OptState
    { osAliases = M.empty
    , osPairs = M.empty
    , osCSE = M.empty
    , osStepsRev = []
    }


buildOptimizeInfo :: SSAOptimizePolicy -> Doctrine -> SSA -> OptimizeInfo
buildOptimizeInfo policy doc ssa =
  let mode = ssaMode ssa
      gens = M.elems (M.findWithDefault M.empty mode (dGens doc))
      aliasUnary =
        case M.lookup mode (mtClassifiedBy (dModes doc)) >>= cdComp of
          Nothing -> S.empty
          Just comp ->
            S.fromList
              [ compCtxExt comp
              , compVar comp
              , compReindex comp
              ]
      dupGens =
        S.fromList
          [ gdName gd
          | gd <- gens
          , isDupShape gd
          ]
      pairTriples = inferPairTriples gens
      pairIntros = S.fromList [ pairIntroGen triple | triple <- pairTriples ]
      pairProjs =
        M.fromList
          [ (pairFstGen triple, ProjFirst)
          | triple <- pairTriples
          ]
          <> M.fromList
            [ (pairSndGen triple, ProjSecond)
            | triple <- pairTriples
            ]
      reusable = pairIntros `S.union` S.fromList (M.keys pairProjs)
      safeDrop = aliasUnary `S.union` dupGens `S.union` pairIntros `S.union` S.fromList (M.keys pairProjs)
   in OptimizeInfo
        { oiPolicy = policy
        , oiAliasUnaryGens = aliasUnary
        , oiDupGens = dupGens
        , oiPairIntroGens = pairIntros
        , oiPairProjGens = pairProjs
        , oiReusableGens = reusable
        , oiSafeDropGens = safeDrop
        }


keepStep :: OptimizeInfo -> SSAStep -> OptState -> OptState
keepStep info step st =
  let st' = st { osStepsRev = step : osStepsRev st }
   in case cseKey info step of
        Nothing -> st'
        Just key -> st' { osCSE = M.insert key (stepOuts step) (osCSE st') }


addAlias :: PortId -> PortId -> OptState -> OptState
addAlias out rep st =
  st { osAliases = M.insert out (resolveAlias (osAliases st) rep) (osAliases st) }


resolveAlias :: M.Map PortId PortId -> PortId -> PortId
resolveAlias aliases = go
  where
    go port =
      case M.lookup port aliases of
        Nothing -> port
        Just next
          | next == port -> port
          | otherwise -> go next


collectUsedPorts :: [PortId] -> [PortId] -> [SSAStep] -> S.Set PortId
collectUsedPorts ins outs steps =
  S.fromList (ins <> outs <> concatMap stepPorts steps)
  where
    stepPorts step =
      case step of
        StepGen{} -> stepIns step <> stepOuts step
        StepBox{} -> stepIns step <> stepOuts step
        StepFeedback{} -> stepIns step <> stepOuts step


filterPortNames :: S.Set PortId -> M.Map PortId a -> M.Map PortId a
filterPortNames used = M.filterWithKey (\port _ -> port `S.member` used)


promoteOutputNames
  :: S.Set PortId
  -> [PortId]
  -> [PortId]
  -> [PortId]
  -> M.Map PortId a
  -> M.Map PortId a
promoteOutputNames _used _inputs _origOuts _newOuts names = names


dceSteps :: OptimizeInfo -> [PortId] -> [SSAStep] -> [SSAStep]
dceSteps info outputs steps =
  fst (foldl' visit ([], S.fromList outputs) (reverse steps))
  where
    visit (kept, used) step =
      let outs = stepOuts step
          usedHere = null outs || any (`S.member` used) outs || not (isDroppable info step)
          used' =
            if usedHere
              then used `S.union` S.fromList (stepIns step)
              else used
          kept' =
            if usedHere
              then step : kept
              else kept
       in (kept', used')


isDroppable :: OptimizeInfo -> SSAStep -> Bool
isDroppable info step =
  case step of
    StepGen{} -> stepGen step `S.member` oiSafeDropGens info
    StepBox{} -> False
    StepFeedback{} -> False


cseKey :: OptimizeInfo -> SSAStep -> Maybe CSEKey
cseKey info step =
  case step of
    StepGen{}
      | null (stepBinders step)
      , stepGen step `S.member` oiReusableGens info
      , length (stepOuts step) == 1 ->
          Just
            CSEKey
              { ckGen = stepGen step
              , ckAttrs = stepAttrs step
              , ckIns = stepIns step
              }
    _ -> Nothing


data PairTriple = PairTriple
  { pairIntroGen :: GenName
  , pairFstGen :: GenName
  , pairSndGen :: GenName
  }


inferPairTriples :: [GenDecl] -> [PairTriple]
inferPairTriples gens =
  [ PairTriple intro fstProj sndProj
  | (ref, intros) <- M.toList introByRef
  , Just intro <- [uniqueOne intros]
  , Just fstProj <- [uniqueOne (M.findWithDefault [] ref fstByRef)]
  , Just sndProj <- [uniqueOne (M.findWithDefault [] ref sndByRef)]
  ]
  where
    introByRef =
      M.fromListWith (<>)
        [ (ref, [gdName gd])
        | gd <- gens
        , Just ref <- [pairIntroRef gd]
        ]
    fstByRef =
      M.fromListWith (<>)
        [ (ref, [gdName gd])
        | gd <- gens
        , Just ref <- [pairProjRef ProjFirst gd]
        ]
    sndByRef =
      M.fromListWith (<>)
        [ (ref, [gdName gd])
        | gd <- gens
        , Just ref <- [pairProjRef ProjSecond gd]
        ]


uniqueOne :: Ord a => [a] -> Maybe a
uniqueOne xs =
  case S.toList (S.fromList xs) of
    [x] -> Just x
    _ -> Nothing


isDupShape :: GenDecl -> Bool
isDupShape gen =
  case (gdTyVars gen, gdAttrs gen, gdDom gen, gdCod gen) of
    ([v], [], [InPort (OVar v1)], [OVar v2, OVar v3]) ->
      v == v1 && v == v2 && v == v3
    _ -> False


pairIntroRef :: GenDecl -> Maybe ObjRef
pairIntroRef gen =
  case (gdTyVars gen, gdAttrs gen, gdDom gen, gdCod gen) of
    ([a, b], [], [InPort (OVar a1), InPort (OVar b1)], [OCon ref [OAObj (OVar a2), OAObj (OVar b2)]])
      | a == a1 && a == a2 && b == b1 && b == b2 ->
          Just ref
    _ ->
      Nothing


pairProjRef :: PairProj -> GenDecl -> Maybe ObjRef
pairProjRef proj gen =
  case (gdTyVars gen, gdAttrs gen, gdDom gen, gdCod gen) of
    ([a, b], [], [InPort (OCon ref [OAObj (OVar a1), OAObj (OVar b1)])], [OVar outV])
      | a == a1 && b == b1 && outV == expected proj a b ->
          Just ref
    _ ->
      Nothing
  where
    expected ProjFirst a _ = a
    expected ProjSecond _ b = b
