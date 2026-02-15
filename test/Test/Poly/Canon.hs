{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Canon
  ( tests
  ) where

import Control.Monad (foldM)
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import Data.Text (Text)
import qualified Data.Text as T
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Strat.Poly.Graph
  ( Diagram(..)
  , PortId(..)
  , EdgePayload(..)
  , emptyDiagram
  , freshPort
  , addEdgePayload
  , reindexDiagramForDisplay
  , canonDiagramRaw
  , validateDiagram
  )
import Strat.Poly.DiagramIso (diagramIsoEq, diagramIsoEqSlow)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeRef(..), TypeName(..))


tests :: TestTree
tests =
  testGroup
    "Poly.Canon"
    [ testProperty "idempotence: canon(canon(d)) = canon(d)" propCanonIdempotent
    , testProperty "agreement with slow isomorphism on small diagrams" propCanonAgreesSlow
    , testCase "regression: display reindex is not canonical" testDisplayReindexNotCanonical
    , testCase "symmetry stress: canonicalization is deterministic" testSymmetryStress
    ]

propCanonIdempotent :: Property
propCanonIdempotent =
  forAll genSmallDiagram $ \diag ->
    case canonDiagramRaw diag of
      Left err ->
        counterexample ("canon failed: " <> T.unpack err) False
      Right c1 ->
        case canonDiagramRaw c1 of
          Left err ->
            counterexample ("canon second pass failed: " <> T.unpack err) False
          Right c2 ->
            c2 === c1

propCanonAgreesSlow :: Property
propCanonAgreesSlow =
  forAll genDiagramPair $ \(d1, d2) ->
    case (diagramIsoEqSlow d1 d2, diagramIsoEq d1 d2) of
      (Right slow, Right fast) ->
        fast === slow
      (Left err, _) ->
        counterexample ("slow iso failed: " <> T.unpack err) False
      (_, Left err) ->
        counterexample ("canon iso failed: " <> T.unpack err) False

testDisplayReindexNotCanonical :: Assertion
testDisplayReindexNotCanonical = do
  d1 <- require (mkCycleDiagram [(0, 1), (2, 3)])
  d2 <- require (mkCycleDiagram [(0, 2), (1, 3)])
  slowIso <- require (diagramIsoEqSlow d1 d2)
  assertBool "expected regression pair to be isomorphic" slowIso
  r1 <- require (reindexDiagramForDisplay d1)
  r2 <- require (reindexDiagramForDisplay d2)
  assertBool "display reindex unexpectedly collapsed the regression pair" (r1 /= r2)
  c1 <- require (canonDiagramRaw d1)
  c2 <- require (canonDiagramRaw d2)
  assertEqual "canon should collapse isomorphic diagrams" c1 c2

testSymmetryStress :: Assertion
testSymmetryStress = do
  base <- require (mkCycleDiagram [(0, 1), (2, 3), (4, 5)])
  variants <-
    mapM
      (require . mkCycleDiagram)
      [ [(0, 2), (1, 4), (3, 5)]
      , [(0, 3), (1, 5), (2, 4)]
      , [(0, 4), (1, 2), (3, 5)]
      ]
  baseCanon <- require (canonDiagramRaw base)
  mapM_
    ( \diag -> do
        canon <- require (canonDiagramRaw diag)
        assertEqual "all symmetric variants should share one canonical form" baseCanon canon
    )
    variants

genDiagramPair :: Gen (Diagram, Diagram)
genDiagramPair = do
  d1 <- genSmallDiagram
  d2 <- genSmallDiagram
  pure (d1, d2)

genSmallDiagram :: Gen Diagram
genSmallDiagram = do
  seedPorts <- chooseInt (0, 2)
  edgeCount <- chooseInt (0, 3)
  let (_, d0) = allocPorts seedPorts (emptyDiagram testMode [])
  dN <- foldM (\d _ -> genStep d) d0 [1 :: Int .. edgeCount]
  let dFinal = finalizeBoundary dN
  case validateDiagram dFinal of
    Left _ -> pure (emptyDiagram testMode [])
    Right () -> pure dFinal
  where
    genStep diag = do
      let consFree =
            [ PortId k
            | (k, Nothing) <- IM.toAscList (dCons diag)
            ]
      inArity <-
        if null consFree
          then pure 0
          else chooseInt (0, min 2 (length consFree))
      ins <- pickDistinct inArity consFree
      outArity <- chooseInt (0, 2)
      let (outs, diag1) = allocPorts outArity diag
      gname <- elements ["g", "h", "k"]
      let payload = PGen (GenName gname) M.empty []
      case addEdgePayload payload ins outs diag1 of
        Left _ -> pure diag
        Right diag2 -> pure diag2

pickDistinct :: Int -> [a] -> Gen [a]
pickDistinct n xs = do
  ys <- shuffle xs
  pure (take n ys)

mkCycleDiagram :: [(Int, Int)] -> Either Text Diagram
mkCycleDiagram pairs = do
  let maxIx =
        case pairs of
          [] -> -1
          _ -> maximum (map fst pairs <> map snd pairs)
  let (ports, d0) = allocPorts (maxIx + 1) (emptyDiagram testMode [])
  let lookupPort i =
        if i < 0 || i >= length ports
          then Left "mkCycleDiagram: invalid port index"
          else Right (ports !! i)
  dN <- foldM (addPair lookupPort) d0 pairs
  let dFinal = dN { dIn = [], dOut = [] }
  validateDiagram dFinal
  pure dFinal
  where
    addPair lookupPort diag (i, j) = do
      pIn <- lookupPort i
      pj <- lookupPort j
      d1 <- addEdgePayload (PGen (GenName "g") M.empty []) [pIn] [pj] diag
      addEdgePayload (PGen (GenName "h") M.empty []) [pj] [pIn] d1

allocPorts :: Int -> Diagram -> ([PortId], Diagram)
allocPorts n = go n []
  where
    go k acc diag
      | k <= 0 = (reverse acc, diag)
      | otherwise =
          let (pid, diag') = freshPort testType diag
           in go (k - 1) (pid : acc) diag'

finalizeBoundary :: Diagram -> Diagram
finalizeBoundary diag =
  let ins =
        [ PortId k
        | (k, Nothing) <- IM.toAscList (dProd diag)
        ]
      outs =
        [ PortId k
        | (k, Nothing) <- IM.toAscList (dCons diag)
        ]
   in diag { dIn = ins, dOut = outs }

testMode :: ModeName
testMode = ModeName "M"

testType :: TypeExpr
testType = TCon (TypeRef testMode (TypeName "A")) []

require :: Either Text a -> IO a
require (Left err) = assertFailure (T.unpack err) >> fail "unreachable"
require (Right x) = pure x
