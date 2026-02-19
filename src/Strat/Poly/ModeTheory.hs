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
  , ModeTheory(..)
  , emptyModeTheory
  , addMode
  , addModDecl
  , addModEqn
  , addModTransformDecl
  , composeMod
  , normalizeModExpr
  , checkWellFormed
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import Strat.Poly.Names (GenName)


newtype ModeName = ModeName Text deriving (Eq, Ord, Show)
newtype ModName = ModName Text deriving (Eq, Ord, Show)
newtype ModTransformName = ModTransformName Text deriving (Eq, Ord, Show)

data ModeInfo = ModeInfo
  { miName :: ModeName
  } deriving (Eq, Show)

data ModDecl = ModDecl
  { mdName :: ModName
  , mdSrc :: ModeName
  , mdTgt :: ModeName
  }
  deriving (Eq, Show)

-- A modality expression is a composition path in application order.
data ModExpr = ModExpr
  { meSrc :: ModeName
  , meTgt :: ModeName
  , mePath :: [ModName]
  }
  deriving (Eq, Ord, Show)

data ModEqn = ModEqn
  { meLHS :: ModExpr
  , meRHS :: ModExpr
  } deriving (Eq, Show)

data ModTransformDecl = ModTransformDecl
  { mtdName :: ModTransformName
  , mtdFrom :: ModExpr
  , mtdTo :: ModExpr
  , mtdWitness :: GenName
  } deriving (Eq, Show)

data ModeTheory = ModeTheory
  { mtModes :: Map ModeName ModeInfo
  , mtDecls :: Map ModName ModDecl
  , mtEqns :: [ModEqn]
  , mtTransforms :: Map ModTransformName ModTransformDecl
  }
  deriving (Eq, Show)


emptyModeTheory :: ModeTheory
emptyModeTheory = ModeTheory M.empty M.empty [] M.empty

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
  where
    checkDecl decl
      | M.member (mdSrc decl) (mtModes mt) && M.member (mdTgt decl) (mtModes mt) = Right ()
      | otherwise = Left "modality declaration uses unknown mode"

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
            [] -> Nothing

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
