{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ModeTheory
  ( ModeName(..)
  , ModName(..)
  , ModTransformName(..)
  , ModeInfo(..)
  , ModExpr(..)
  , ModDecl(..)
  , ModEqn(..)
  , ModTransformDecl(..)
  , ClassificationDecl(..)
  , ModeTheory(..)
  , emptyModeTheory
  , addMode
  , addModDecl
  , addModEqn
  , addModTransformDecl
  , addClassification
  , classificationDeps
  , classificationOrder
  , composeMod
  , normalizeModExpr
  , checkWellFormed
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import qualified Data.Set as S
import Strat.Poly.ModeSyntax
import Strat.Poly.Syntax (Obj(..))


data ModeInfo = ModeInfo
  { miName :: ModeName
  } deriving (Eq, Show)

data ClassificationDecl = ClassificationDecl
  { cdClassifier :: ModeName
  , cdUniverse :: Obj
  , cdTag :: Maybe Text
  } deriving (Eq, Show)

data ModeTheory = ModeTheory
  { mtModes :: Map ModeName ModeInfo
  , mtDecls :: Map ModName ModDecl
  , mtEqns :: [ModEqn]
  , mtTransforms :: Map ModTransformName ModTransformDecl
  , mtClassifiedBy :: Map ModeName ClassificationDecl
  }
  deriving (Eq, Show)


emptyModeTheory :: ModeTheory
emptyModeTheory = ModeTheory M.empty M.empty [] M.empty M.empty

addMode :: ModeName -> ModeTheory -> Either Text ModeTheory
addMode name mt
  | M.member name (mtModes mt) = Left "duplicate mode name"
  | otherwise =
      let info = ModeInfo { miName = name }
      in Right mt { mtModes = M.insert name info (mtModes mt) }

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
          | cdClassifier decl /= mode -> [cdClassifier decl]
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

normalizeModExpr :: ModeTheory -> ModExpr -> ModExpr
normalizeModExpr mt = go
  where
    go me =
      case rewriteOnce mt me of
        Nothing -> me
        Just me' -> go me'

checkWellFormed :: ModeTheory -> Either Text ()
checkWellFormed mt = do
  if M.null (mtModes mt)
    then Left "mode theory: no modes declared"
    else Right ()
  mapM_ checkDecl (M.elems (mtDecls mt))
  mapM_ (validateModEqn mt) (mtEqns mt)
  mapM_ (validateModTransformDecl mt) (M.elems (mtTransforms mt))
  checkClassificationWellFormed mt
  checkClassificationStratifiable mt
  where
    checkDecl decl
      | M.member (mdSrc decl) (mtModes mt) && M.member (mdTgt decl) (mtModes mt) = Right ()
      | otherwise = Left "modality declaration uses unknown mode"

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
  if length (mePath (meRHS eqn)) < length (mePath (meLHS eqn))
    then Right ()
    else Left "mode theory: modality equation must strictly decrease path length"

requireModDecl :: ModeTheory -> ModName -> Either Text ModDecl
requireModDecl mt name =
  case M.lookup name (mtDecls mt) of
    Nothing -> Left "mode theory: unknown modality"
    Just decl -> Right decl

rewriteOnce :: ModeTheory -> ModExpr -> Maybe ModExpr
rewriteOnce mt me =
  case findRewrite 0 (mePath me) of
    Nothing -> Nothing
    Just path' ->
      case mkExprFromPath mt (meSrc me) path' of
        Right me' -> Just me'
        Left _ -> Nothing
  where
    findRewrite _ [] = Nothing
    findRewrite idx path =
      case firstRule path (mtEqns mt) of
        Just (lhsLen, rhsPath) ->
          let (prefix, rest) = splitAt idx (mePath me)
              suffix = drop lhsLen rest
          in Just (prefix <> rhsPath <> suffix)
        Nothing ->
          case path of
            (_:xs) -> findRewrite (idx + 1) xs

    firstRule _ [] = Nothing
    firstRule path (eqn:eqns) =
      let lhsPath = mePath (meLHS eqn)
      in if matchesPrefix lhsPath path
          then Just (length lhsPath, mePath (meRHS eqn))
          else firstRule path eqns

matchesPrefix :: Eq a => [a] -> [a] -> Bool
matchesPrefix [] _ = True
matchesPrefix _ [] = False
matchesPrefix (x:xs) (y:ys) = x == y && matchesPrefix xs ys

mkExprFromPath :: ModeTheory -> ModeName -> [ModName] -> Either Text ModExpr
mkExprFromPath mt src path = do
  tgt <- walk src path
  Right ModExpr { meSrc = src, meTgt = tgt, mePath = path }
  where
    walk cur [] = Right cur
    walk cur (m:ms) = do
      decl <- requireModDecl mt m
      if mdSrc decl == cur
        then walk (mdTgt decl) ms
        else Left "mode theory: modality composition type mismatch"

objMode0 :: Obj -> ModeName
objMode0 = objOwnerMode
