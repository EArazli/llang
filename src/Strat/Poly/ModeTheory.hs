{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.ModeTheory
  ( ModeName(..)
  , ModName(..)
  , VarDiscipline(..)
  , canUpgrade
  , upgradeDiscipline
  , ModeInfo(..)
  , ModExpr(..)
  , ModDecl(..)
  , ModEqn(..)
  , AdjDecl(..)
  , ModeTheory(..)
  , emptyModeTheory
  , addMode
  , setModeDiscipline
  , addModDecl
  , addModEqn
  , addAdjDecl
  , composeMod
  , modeDiscipline
  , allowsDrop
  , allowsDup
  , normalizeModExpr
  , checkWellFormed
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)


newtype ModeName = ModeName Text deriving (Eq, Ord, Show)
newtype ModName = ModName Text deriving (Eq, Ord, Show)


data VarDiscipline = Linear | Affine | Relevant | Cartesian
  deriving (Eq, Ord, Show, Read)

canUpgrade :: VarDiscipline -> VarDiscipline -> Bool
canUpgrade old new =
  case (old, new) of
    (Linear, _) -> True
    (Affine, Affine) -> True
    (Affine, Cartesian) -> True
    (Relevant, Relevant) -> True
    (Relevant, Cartesian) -> True
    (Cartesian, Cartesian) -> True
    _ -> False

upgradeDiscipline :: VarDiscipline -> VarDiscipline -> Either Text VarDiscipline
upgradeDiscipline old new =
  if canUpgrade old new
    then Right new
    else Left "mode theory: discipline downgrade is not allowed"


data ModeInfo = ModeInfo
  { miName :: ModeName
  , miDiscipline :: VarDiscipline
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

data AdjDecl = AdjDecl
  { adLeft :: ModName
  , adRight :: ModName
  } deriving (Eq, Show)


data ModeTheory = ModeTheory
  { mtModes :: Map ModeName ModeInfo
  , mtDecls :: Map ModName ModDecl
  , mtEqns :: [ModEqn]
  , mtAdjs :: [AdjDecl]
  }
  deriving (Eq, Show)


emptyModeTheory :: ModeTheory
emptyModeTheory = ModeTheory M.empty M.empty [] []

modeDiscipline :: ModeTheory -> ModeName -> Either Text VarDiscipline
modeDiscipline mt mode =
  case M.lookup mode (mtModes mt) of
    Nothing -> Left "mode theory: unknown mode"
    Just info -> Right (miDiscipline info)

allowsDrop :: VarDiscipline -> Bool
allowsDrop d =
  case d of
    Affine -> True
    Cartesian -> True
    _ -> False

allowsDup :: VarDiscipline -> Bool
allowsDup d =
  case d of
    Relevant -> True
    Cartesian -> True
    _ -> False

addMode :: ModeName -> ModeTheory -> Either Text ModeTheory
addMode name mt
  | M.member name (mtModes mt) = Left "duplicate mode name"
  | otherwise =
      let info = ModeInfo { miName = name, miDiscipline = Linear }
      in Right mt { mtModes = M.insert name info (mtModes mt) }

setModeDiscipline :: ModeName -> VarDiscipline -> ModeTheory -> Either Text ModeTheory
setModeDiscipline mode newDisc mt =
  case M.lookup mode (mtModes mt) of
    Nothing -> Left "mode theory: unknown mode"
    Just info -> do
      disc' <- upgradeDiscipline (miDiscipline info) newDisc
      let info' = info { miDiscipline = disc' }
      Right mt { mtModes = M.insert mode info' (mtModes mt) }

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

addAdjDecl :: AdjDecl -> ModeTheory -> Either Text ModeTheory
addAdjDecl adj mt = do
  validateAdj mt adj
  Right mt { mtAdjs = mtAdjs mt <> [adj] }

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
  mapM_ (validateAdj mt) (mtAdjs mt)
  where
    checkDecl decl
      | M.member (mdSrc decl) (mtModes mt) && M.member (mdTgt decl) (mtModes mt) = Right ()
      | otherwise = Left "modality declaration uses unknown mode"

validateAdj :: ModeTheory -> AdjDecl -> Either Text ()
validateAdj mt adj = do
  left <- requireModDecl mt (adLeft adj)
  right <- requireModDecl mt (adRight adj)
  if mdSrc left == mdTgt right && mdTgt left == mdSrc right
    then Right ()
    else Left "adjunction modalities must have opposite directions"

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
