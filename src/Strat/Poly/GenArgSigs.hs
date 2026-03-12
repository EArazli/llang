{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.GenArgSigs
  ( withStructuralZeroParamGenArgSigs
  ) where

import Control.Applicative ((<|>))
import Control.Monad (foldM)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Poly.Graph
  ( BinderArg(..)
  , Diagram(..)
  , Edge(..)
  , EdgePayload(..)
  )
import Strat.Poly.Names (GenName)
import Strat.Poly.Obj (CodeArg(..), TermDiagram(..))
import Strat.Poly.TypeTheory (GenArgSig(..), TypeTheory(..), lookupGenArgSig)

withStructuralZeroParamGenArgSigs :: [Diagram] -> TypeTheory -> Either Text TypeTheory
withStructuralZeroParamGenArgSigs diags tt = do
  inferred <- foldM collectDiagram M.empty diags
  pure tt { ttGenArgSigs = M.unionWith M.union inferred (ttGenArgSigs tt) }
  where
    collectDiagram acc diag =
      foldM (collectPayload (dMode diag)) acc (map ePayload (IM.elems (dEdges diag)))

    collectPayload mode acc payload =
      case payload of
        PGen g args bargs -> do
          acc1 <- ensureSig mode g args acc
          acc2 <- foldM collectCodeArg acc1 args
          foldM collectBinderArg acc2 bargs
        PBox _ inner ->
          collectDiagram acc inner
        PFeedback inner ->
          collectDiagram acc inner
        PSplice _ _ ->
          Right acc
        PTmMeta _ ->
          Right acc
        PTmLit _ ->
          Right acc
        PInternalDrop ->
          Right acc

    collectCodeArg acc arg =
      case arg of
        CAObj _ -> Right acc
        CATm (TermDiagram inner) -> collectDiagram acc inner

    collectBinderArg acc barg =
      case barg of
        BAConcrete inner -> collectDiagram acc inner
        BAMeta _ -> Right acc

    ensureSig mode g args acc =
      case lookupInferred mode g acc <|> lookupGenArgSig tt mode g of
        Just _ -> Right acc
        Nothing
          | null args ->
              Right (M.insertWith M.union mode (M.singleton g (GenArgSig [])) acc)
          | otherwise ->
              Left
                ( "withStructuralZeroParamGenArgSigs: missing generator arg signature for "
                    <> renderGenName g
                )

    lookupInferred mode g inferred =
      M.lookup g =<< M.lookup mode inferred

    renderGenName :: GenName -> Text
    renderGenName = T.pack . show
