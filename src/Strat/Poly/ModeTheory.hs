{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ModeTheory
  ( ModeName(..)
  , ModName(..)
  , ModTransformName(..)
  , DefEqEngine(..)
  , ModeInfo(..)
  , CompDecl(..)
  , ModExpr(..)
  , ModDecl(..)
  , ModEqn(..)
  , ModTransformDecl(..)
  , ClassificationDecl(..)
  , ModeTheory(..)
  , emptyModeTheory
  , addMode
  , setModeDefEqEngine
  , addModDecl
  , addModEqn
  , addModTransformDecl
  , addClassification
  , addClassifierLift
  , classifierLiftForModality
  , classifierLiftForModExpr
  , classificationDeps
  , classificationOrder
  , composeMod
  , normalizeModExpr
  , modeDefEqEngine
  , checkWellFormed
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import qualified Data.Set as S
import Control.Monad (foldM)
import Strat.Poly.ModeSyntax
import Strat.Poly.Syntax (Obj(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Term.AST (TermExpr(..), TermHeadArg(..))
import Strat.Poly.Term.Normalize (normalizeTermExpr)
import Strat.Poly.Term.RewriteSystem (TRS, TRule(..), mkTRS)
import Strat.Poly.Term.Termination (checkTerminatingSCT)
import Strat.Poly.Term.Confluence (checkConfluent)


data DefEqEngine
  = DefEqTRS
  | DefEqNBE
  deriving (Eq, Ord, Read, Show)

data ModeInfo = ModeInfo
  { miName :: ModeName
  , miDefEqEngine :: DefEqEngine
  } deriving (Eq, Read, Show)

data CompDecl = CompDecl
  { compCtxExt :: GenName
  , compVar :: GenName
  , compReindex :: GenName
  } deriving (Eq, Read, Show)

data ClassificationDecl = ClassificationDecl
  { cdClassifier :: ModeName
  , cdUniverse :: Obj
  , cdComp :: Maybe CompDecl
  } deriving (Eq, Read, Show)

data ModeTheory = ModeTheory
  { mtModes :: Map ModeName ModeInfo
  , mtDecls :: Map ModName ModDecl
  , mtEqns :: [ModEqn]
  , mtTransforms :: Map ModTransformName ModTransformDecl
  , mtClassifiedBy :: Map ModeName ClassificationDecl
  , mtClassifierLifts :: Map ModName ModExpr
  }
  deriving (Eq, Read, Show)


emptyModeTheory :: ModeTheory
emptyModeTheory = ModeTheory M.empty M.empty [] M.empty M.empty M.empty

addMode :: ModeName -> ModeTheory -> Either Text ModeTheory
addMode name mt
  | M.member name (mtModes mt) = Left "duplicate mode name"
  | otherwise =
      let info = ModeInfo { miName = name, miDefEqEngine = DefEqTRS }
      in Right mt { mtModes = M.insert name info (mtModes mt) }

setModeDefEqEngine :: ModeName -> DefEqEngine -> ModeTheory -> Either Text ModeTheory
setModeDefEqEngine mode engine mt =
  case M.lookup mode (mtModes mt) of
    Nothing -> Left "mode theory: defeq engine set for unknown mode"
    Just info ->
      Right
        mt
          { mtModes =
              M.insert mode (info { miDefEqEngine = engine }) (mtModes mt)
          }

addModDecl :: ModDecl -> ModeTheory -> Either Text ModeTheory
addModDecl decl mt
  | M.member (mdName decl) (mtDecls mt) = Left "duplicate modality name"
  | otherwise =
      if M.member (mdSrc decl) (mtModes mt) && M.member (mdTgt decl) (mtModes mt)
        then Right mt { mtDecls = M.insert (mdName decl) decl (mtDecls mt) }
        else Left "modality declaration uses unknown mode"

addModEqn :: ModEqn -> ModeTheory -> Either Text ModeTheory
addModEqn eqn mt = do
  validateModEqn mt eqn
  Right mt { mtEqns = mtEqns mt <> [eqn] }

addModTransformDecl :: ModTransformDecl -> ModeTheory -> Either Text ModeTheory
addModTransformDecl decl mt = do
  validateModExpr mt (mtdFrom decl)
  validateModExpr mt (mtdTo decl)
  if meSrc (mtdFrom decl) == meSrc (mtdTo decl) && meTgt (mtdFrom decl) == meTgt (mtdTo decl)
    then Right ()
    else Left "mode theory: modality transform source/target mismatch"
  if M.member (mtdName decl) (mtTransforms mt)
    then Left "duplicate modality transform name"
    else Right mt { mtTransforms = M.insert (mtdName decl) decl (mtTransforms mt) }

addClassification :: ModeName -> ClassificationDecl -> ModeTheory -> Either Text ModeTheory
addClassification mode decl mt = do
  if M.member mode (mtModes mt)
    then Right ()
    else Left "mode theory: classifiedBy uses unknown mode"
  if M.member mode (mtClassifiedBy mt)
    then Left "mode theory: classifiedBy duplicate for mode"
    else Right ()
  if objMode0 (cdUniverse decl) == cdClassifier decl
    then Right ()
    else Left "mode theory: classifiedBy universe mode mismatch"
  Right mt { mtClassifiedBy = M.insert mode decl (mtClassifiedBy mt) }

addClassifierLift :: ModName -> ModExpr -> ModeTheory -> Either Text ModeTheory
addClassifierLift modName liftExpr mt = do
  baseDecl <-
    case M.lookup modName (mtDecls mt) of
      Nothing -> Left "mode theory: classifier lift references unknown modality"
      Just decl -> Right decl
  let srcClassifier = modeClassifierModeLocal mt (mdSrc baseDecl)
  let tgtClassifier = modeClassifierModeLocal mt (mdTgt baseDecl)
  validateModExpr mt liftExpr
  if meSrc liftExpr == srcClassifier && meTgt liftExpr == tgtClassifier
    then Right ()
    else Left "mode theory: classifier lift source/target mismatch"
  if M.member modName (mtClassifierLifts mt)
    then Left "mode theory: duplicate classifier lift for modality"
    else Right mt { mtClassifierLifts = M.insert modName liftExpr (mtClassifierLifts mt) }

classifierLiftForModality :: ModeTheory -> ModName -> Either Text ModExpr
classifierLiftForModality mt modName = do
  decl <-
    case M.lookup modName (mtDecls mt) of
      Nothing -> Left "mode theory: unknown modality"
      Just d -> Right d
  let srcClassifier = modeClassifierModeLocal mt (mdSrc decl)
  let tgtClassifier = modeClassifierModeLocal mt (mdTgt decl)
  case M.lookup modName (mtClassifierLifts mt) of
    Just me -> do
      if meSrc me == srcClassifier && meTgt me == tgtClassifier
        then Right me
        else Left "mode theory: classifier lift source/target mismatch"
    Nothing ->
      if srcClassifier == mdSrc decl && tgtClassifier == mdTgt decl
        then
          Right
            ModExpr
              { meSrc = mdSrc decl
              , meTgt = mdTgt decl
              , mePath = [modName]
              }
        else
          Left
            ( "mode theory: missing explicit classifier lift for modality "
                <> renderMod modName
            )

classifierLiftForModExpr :: ModeTheory -> ModExpr -> Either Text ModExpr
classifierLiftForModExpr mt me = do
  validateModExpr mt me
  let srcClass = modeClassifierMode (meSrc me)
  let tgtClass = modeClassifierMode (meTgt me)
  let start =
        ModExpr
          { meSrc = srcClass
          , meTgt = srcClass
          , mePath = []
          }
  stepLifts <- mapM (classifierLiftForModality mt) (mePath me)
  composed <- foldM (composeMod mt) start stepLifts
  let normalized = normalizeModExpr mt composed
  if meSrc normalized == srcClass && meTgt normalized == tgtClass
    then Right normalized
    else Left "mode theory: classifier lift composition has wrong endpoints"
  where
    modeClassifierMode mode =
      case M.lookup mode (mtClassifiedBy mt) of
        Nothing -> mode
        Just decl -> cdClassifier decl

classificationDeps :: ModeTheory -> Map ModeName [ModeName]
classificationDeps mt =
  M.fromList
    [ (mode, edgeDeps mode)
    | mode <- M.keys (mtModes mt)
    ]
  where
    edgeDeps mode =
      case M.lookup mode (mtClassifiedBy mt) of
        Just decl
          | cdClassifier decl /= mode
          , M.member (cdClassifier decl) (mtModes mt) ->
              [cdClassifier decl]
        _ -> []

classificationOrder :: ModeTheory -> Either Text [ModeName]
classificationOrder mt = do
  let modes = M.keys (mtModes mt)
  (_, doneFinal, postRev) <- foldl step (Right (S.empty, S.empty, [])) modes
  if S.size doneFinal == length modes
    then Right (reverse postRev)
    else Left "mode theory: classification order incomplete"
  where
    step acc mode = do
      st <- acc
      dfs mode st

    dfs mode st@(visiting, done, postRev)
      | mode `S.member` done = Right st
      | mode `S.member` visiting =
          Left ("mode theory: classification cycle detected at " <> renderMode mode)
      | otherwise = do
          let visiting' = S.insert mode visiting
          st' <- foldl stepDep (Right (visiting', done, postRev)) (M.findWithDefault [] mode (classificationDeps mt))
          let (visitingDone, doneDone, postRevDone) = st'
          let visitingFinal = S.delete mode visitingDone
          let doneFinal = S.insert mode doneDone
          Right (visitingFinal, doneFinal, mode : postRevDone)

    stepDep acc dep = do
      st <- acc
      dfs dep st

    renderMode (ModeName name) = name

composeMod :: ModeTheory -> ModExpr -> ModExpr -> Either Text ModExpr
composeMod _ f g
  | meTgt f /= meSrc g = Left "mode mismatch in modality composition"
  | otherwise =
      Right
        ModExpr
          { meSrc = meSrc f
          , meTgt = meTgt g
          , mePath = mePath f <> mePath g
          }

-- Internal encoding of modality paths as unary TermExpr spines.
-- A path m1.m2...mk is encoded as m1(m2(...(mk(__mod_id))...)).
-- `__mod_id` is a nullary constant that cannot clash with user identifiers
-- (user identifiers must start with a letter; `__mod_id` starts with `_`).
modEqIdFun :: GenName
modEqIdFun = GenName "__mod_id"

modEqIdTerm :: TermExpr
modEqIdTerm = TMGen modEqIdFun []

-- Diagnostic-only mode name for the TRS checks; cannot clash with user modes.
modEqDiagnosticMode :: ModeName
modEqDiagnosticMode = ModeName "__mod_eq"

encodeModPathWithTail :: [ModName] -> TermExpr -> TermExpr
encodeModPathWithTail mods tail0 =
  foldr (\(ModName m) acc -> TMGen (GenName m) [THATm acc]) tail0 mods

decodeModPathFromTerm :: TermExpr -> Maybe [ModName]
decodeModPathFromTerm = go
  where
    go (TMGen f []) | f == modEqIdFun = Just []
    go (TMGen f [THATm inner]) | f /= modEqIdFun = do
      rest <- go inner
      case f of
        GenName nm -> Just (ModName nm : rest)
    go _ = Nothing

modExprToTerm :: ModExpr -> TermExpr
modExprToTerm me = encodeModPathWithTail (mePath me) modEqIdTerm

renderModeName :: ModeName -> Text
renderModeName (ModeName n) = n

renderModExprShort :: ModExpr -> Text
renderModExprShort me =
  case mePath me of
    [] -> "id@" <> renderModeName (meSrc me)
    ms -> T.intercalate "." (map renderMod ms)

modEqRuleToTRule :: Int -> ModEqn -> TRule
modEqRuleToTRule i (ModEqn lhs rhs) =
  TRule
    { trName = "mod_eq[" <> T.pack (show i) <> "] "
               <> renderModExprShort lhs <> " -> " <> renderModExprShort rhs
    , trLHS  = encodeModPathWithTail (mePath lhs) (TMBound 0)
    , trRHS  = encodeModPathWithTail (mePath rhs) (TMBound 0)
    }

modEqTRS :: ModeTheory -> TRS
modEqTRS mt =
  mkTRS modEqDiagnosticMode (zipWith modEqRuleToTRule [0..] (mtEqns mt))

normalizeModExpr :: ModeTheory -> ModExpr -> ModExpr
normalizeModExpr mt me
  | null (mtEqns mt) = me
  | otherwise =
      let trs   = modEqTRS mt
          term0 = modExprToTerm me
          termN = normalizeTermExpr trs term0
      in case decodeModPathFromTerm termN of
           Just pathN -> me { mePath = pathN }
           Nothing    -> me

checkWellFormed :: ModeTheory -> Either Text ()
checkWellFormed mt = do
  if M.null (mtModes mt)
    then Left "mode theory: no modes declared"
  else Right ()
  mapM_ checkDecl (M.elems (mtDecls mt))
  mapM_ (validateModEqn mt) (mtEqns mt)
  let trs = modEqTRS mt
  case checkTerminatingSCT trs of
    Left err -> Left ("mode theory: mod_eq termination not proven: " <> err)
    Right () -> pure ()
  case checkConfluent trs of
    Left err -> Left ("mode theory: mod_eq confluence failed: " <> err)
    Right () -> pure ()
  mapM_ (validateModTransformDecl mt) (M.elems (mtTransforms mt))
  mapM_ (validateClassifierLiftDecl mt) (M.toList (mtClassifierLifts mt))
  validateClassifierLifts mt
  validateClassifierLiftsCoherent mt
  checkClassificationWellFormed mt
  checkClassificationStratifiable mt
  where
    checkDecl decl
      | M.member (mdSrc decl) (mtModes mt) && M.member (mdTgt decl) (mtModes mt) = Right ()
      | otherwise = Left "modality declaration uses unknown mode"

validateClassifierLiftDecl :: ModeTheory -> (ModName, ModExpr) -> Either Text ()
validateClassifierLiftDecl mt (modName, liftExpr) = do
  decl <-
    case M.lookup modName (mtDecls mt) of
      Nothing -> Left "mode theory: classifier lift references unknown modality"
      Just d -> Right d
  let srcClassifier = modeClassifierModeLocal mt (mdSrc decl)
  let tgtClassifier = modeClassifierModeLocal mt (mdTgt decl)
  validateModExpr mt liftExpr
  if meSrc liftExpr == srcClassifier && meTgt liftExpr == tgtClassifier
    then Right ()
    else Left "mode theory: classifier lift source/target mismatch"

validateClassifierLifts :: ModeTheory -> Either Text ()
validateClassifierLifts mt =
  mapM_ checkOne (M.toList (mtDecls mt))
  where
    checkOne (modName, decl) =
      let srcClassifier = modeClassifierModeLocal mt (mdSrc decl)
          tgtClassifier = modeClassifierModeLocal mt (mdTgt decl)
          needsExplicit =
            srcClassifier /= mdSrc decl || tgtClassifier /= mdTgt decl
       in case M.lookup modName (mtClassifierLifts mt) of
            Just liftExpr ->
              if meSrc liftExpr == srcClassifier && meTgt liftExpr == tgtClassifier
                then Right ()
                else Left "mode theory: classifier lift source/target mismatch"
            Nothing ->
              if needsExplicit
                then
                  Left
                    ( "mode theory: missing explicit classifier lift for modality "
                        <> renderMod modName
                    )
                else Right ()

validateClassifierLiftsCoherent :: ModeTheory -> Either Text ()
validateClassifierLiftsCoherent mt =
  mapM_ checkEqn (mtEqns mt)
  where
    checkEqn eqn = do
      lhsLift <- classifierLiftForModExpr mt (meLHS eqn)
      rhsLift <- classifierLiftForModExpr mt (meRHS eqn)
      let lhsNorm = normalizeModExpr mt lhsLift
      let rhsNorm = normalizeModExpr mt rhsLift
      if lhsNorm == rhsNorm
        then Right ()
        else
          Left
            ( "mode theory: classifier lift coherence failed for modality equation "
                <> T.pack (show (meLHS eqn))
                <> " -> "
                <> T.pack (show (meRHS eqn))
                <> " (lhs lift "
                <> T.pack (show lhsNorm)
                <> ", rhs lift "
                <> T.pack (show rhsNorm)
                <> ")"
            )

checkClassificationWellFormed :: ModeTheory -> Either Text ()
checkClassificationWellFormed mt =
  mapM_ checkOne (M.toList (mtClassifiedBy mt))
  where
    checkOne (mode, decl) = do
      if M.member mode (mtModes mt)
        then Right ()
        else Left "mode theory: classifiedBy uses unknown mode"
      if M.member (cdClassifier decl) (mtModes mt)
        then Right ()
        else Left "mode theory: classifiedBy uses unknown mode"
      if objMode0 (cdUniverse decl) == cdClassifier decl
        then Right ()
        else Left "mode theory: classifiedBy universe mode mismatch"

checkClassificationStratifiable :: ModeTheory -> Either Text ()
checkClassificationStratifiable mt =
  case classificationOrder mt of
    Left err -> Left err
    Right _ -> Right ()

validateModTransformDecl :: ModeTheory -> ModTransformDecl -> Either Text ()
validateModTransformDecl mt decl = do
  validateModExpr mt (mtdFrom decl)
  validateModExpr mt (mtdTo decl)
  if meSrc (mtdFrom decl) == meSrc (mtdTo decl) && meTgt (mtdFrom decl) == meTgt (mtdTo decl)
    then Right ()
    else Left "mode theory: modality transform source/target mismatch"

validateModExpr :: ModeTheory -> ModExpr -> Either Text ()
validateModExpr mt me = do
  if M.member (meSrc me) (mtModes mt)
    then Right ()
    else Left "mode theory: modality expression has unknown source mode"
  if M.member (meTgt me) (mtModes mt)
    then Right ()
    else Left "mode theory: modality expression has unknown target mode"
  actualTgt <- walk (meSrc me) (mePath me)
  if actualTgt == meTgt me
    then Right ()
    else Left "mode theory: ill-typed modality expression"
  where
    walk cur [] = Right cur
    walk cur (m:ms) = do
      decl <- requireModDecl mt m
      if mdSrc decl == cur
        then walk (mdTgt decl) ms
        else Left "mode theory: modality composition type mismatch"

modeDefEqEngine :: ModeTheory -> ModeName -> DefEqEngine
modeDefEqEngine mt mode =
  case M.lookup mode (mtModes mt) of
    Just info -> miDefEqEngine info
    Nothing -> DefEqTRS

validateModEqn :: ModeTheory -> ModEqn -> Either Text ()
validateModEqn mt eqn = do
  validateModExpr mt (meLHS eqn)
  validateModExpr mt (meRHS eqn)
  if null (mePath (meLHS eqn))
    then Left "mode theory: modality equation LHS must be non-empty"
    else Right ()
  if meSrc (meLHS eqn) == meSrc (meRHS eqn) && meTgt (meLHS eqn) == meTgt (meRHS eqn)
    then Right ()
    else Left "mode theory: modality equation source/target mismatch"

requireModDecl :: ModeTheory -> ModName -> Either Text ModDecl
requireModDecl mt name =
  case M.lookup name (mtDecls mt) of
    Nothing -> Left "mode theory: unknown modality"
    Just decl -> Right decl

objMode0 :: Obj -> ModeName
objMode0 = objOwnerMode

modeClassifierModeLocal :: ModeTheory -> ModeName -> ModeName
modeClassifierModeLocal mt mode =
  case M.lookup mode (mtClassifiedBy mt) of
    Nothing -> mode
    Just decl -> cdClassifier decl

renderMod :: ModName -> Text
renderMod (ModName name) = name
