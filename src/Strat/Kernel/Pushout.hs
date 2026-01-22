{-# LANGUAGE OverloadedStrings #-}
module Strat.Kernel.Pushout
  ( PushoutResult(..)
  , computePushout
  ) where

import Strat.Kernel.Morphism
import Strat.Kernel.Morphism.Util (symbolMapMorphism, isSymbolMap)
import Strat.Kernel.Presentation
import Strat.Kernel.Presentation.Merge (mergePresentations)
import Strat.Kernel.Presentation.Rename (renameOpsPresentation, renameSortsPresentation)
import Strat.Kernel.Signature (sigSortCtors, sigOps)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Text (Text)
import Control.Monad (foldM)

data PushoutResult = PushoutResult
  { poPres  :: Presentation
  , poInl   :: Morphism
  , poInr   :: Morphism
  , poGlue  :: Morphism
  }
  deriving (Eq, Show)

computePushout :: Text -> Morphism -> Morphism -> Either Text PushoutResult
computePushout name f g = do
  ensureSameSource
  opMapF <- requireSymbolMap f
  opMapG <- requireSymbolMap g
  ensureInjective "sort" (morSortMap f) (interfaceSorts f)
  ensureInjective "sort" (morSortMap g) (interfaceSorts g)
  ensureInjective "op" opMapF (interfaceOps f)
  ensureInjective "op" opMapG (interfaceOps g)
  let renameSortB = buildRenameMap (morSortMap f) (interfaceSorts f)
  let renameSortC = buildRenameMap (morSortMap g) (interfaceSorts g)
  let renameOpB = buildRenameMap opMapF (interfaceOps f)
  let renameOpC = buildRenameMap opMapG (interfaceOps g)
  b' <- renamePresentation renameSortB renameOpB (morTgt f)
  c' <- renamePresentation renameSortC renameOpC (morTgt g)
  presMerged <- mergePresentationsList [morSrc f, b', c']
  let pres = presMerged { presName = name }
  glue0 <- buildGlue pres
  inl0 <- buildInj (morTgt f) pres renameSortB renameOpB
  inr0 <- buildInj (morTgt g) pres renameSortC renameOpC
  let glue = glue0 { morName = name <> ".glue" }
  let inl = inl0 { morName = name <> ".inl" }
  let inr = inr0 { morName = name <> ".inr" }
  mapM_ (checkGenerated (morName glue)) [glue]
  mapM_ (checkGenerated (morName inl)) [inl]
  mapM_ (checkGenerated (morName inr)) [inr]
  pure PushoutResult { poPres = pres, poInl = inl, poInr = inr, poGlue = glue }
  where
    ensureSameSource =
      if morSrc f == morSrc g
        then Right ()
        else Left "pushout requires morphisms with the same source"

    requireSymbolMap mor =
      case isSymbolMap mor of
        Left err ->
          Left ("pushout currently requires symbol-map morphisms (op ↦ op(args…)); got general term interpretation for op " <> extractOp err)
        Right mp -> Right mp

    extractOp err =
      case T.stripPrefix "Non-symbol op mapping for " err of
        Just op -> op
        Nothing ->
          case T.stripPrefix "Missing op mapping: " err of
            Just op -> op
            Nothing -> err

    interfaceSorts mor = M.keys (sigSortCtors (presSig (morSrc mor)))
    interfaceOps mor = M.keys (sigOps (presSig (morSrc mor)))

    ensureInjective label mapping keys = do
      let images = [ M.findWithDefault k k mapping | k <- keys ]
      case firstDup images of
        Nothing -> Right ()
        Just dup -> Left ("pushout requires injective " <> label <> " mapping on interface image: " <> renderName dup)

    firstDup xs = go S.empty xs
      where
        go _ [] = Nothing
        go seen (x:rest)
          | x `S.member` seen = Just x
          | otherwise = go (S.insert x seen) rest

    buildRenameMap mapping keys =
      M.fromList
        [ (tgt, src)
        | src <- keys
        , let tgt = M.findWithDefault src src mapping
        ]

    renamePresentation sortMap opMap pres = do
      pres1 <- renameSortsPresentation (renameSort sortMap) pres
      renameOpsPresentation (renameOp opMap) pres1

    renameSort m name = M.findWithDefault name name m
    renameOp m name = M.findWithDefault name name m

    mergePresentationsList [] = Left "pushout internal error: no presentations"
    mergePresentationsList (p:ps) = foldM mergePresentations p ps

    buildGlue pres = do
      let sorts = M.keys (sigSortCtors (presSig (morSrc f)))
      let ops = M.keys (sigOps (presSig (morSrc f)))
      let sortMap = M.fromList [ (s, s) | s <- sorts ]
      let opMap = M.fromList [ (o, o) | o <- ops ]
      symbolMapMorphism (morSrc f) pres sortMap opMap

    buildInj srcPres tgtPres sortRen opRen = do
      let sorts = M.keys (sigSortCtors (presSig srcPres))
      let ops = M.keys (sigOps (presSig srcPres))
      let sortMap = M.fromList [ (s, renameSort sortRen s) | s <- sorts ]
      let opMap = M.fromList [ (o, renameOp opRen o) | o <- ops ]
      symbolMapMorphism srcPres tgtPres sortMap opMap

    checkGenerated label mor =
      case checkMorphism (mcPolicy (morCheck mor)) (mcFuel (morCheck mor)) mor of
        Left err -> Left ("pushout generated morphism " <> label <> " invalid: " <> T.pack (show err))
        Right () -> Right ()

renderName :: Show a => a -> Text
renderName = T.pack . show
