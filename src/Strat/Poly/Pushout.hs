{-# LANGUAGE OverloadedStrings #-}
module Strat.Poly.Pushout
  ( PolyPushoutResult(..)
  , computePolyPushout
  , computePolyPushoutPreferRight
  , computePolyCoproduct
  , mkInclusionMorphism
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM
import Control.Monad (filterM, foldM)
import Data.Functor.Identity (runIdentity)
import Strat.Common.Rules (RewritePolicy(..))
import Strat.Common.Rules (RuleClass(..), Orientation(..))
import Strat.Poly.Doctrine
import Strat.Poly.Morphism
import Strat.Poly.ModeTheory
  ( ModeName(..)
  , ModeTheory(..)
  , ModeInfo(..)
  , ModName(..)
  , ModDecl(..)
  , ModEqn(..)
  , ModExpr(..)
  , ModTransformName(..)
  , ModTransformDecl(..)
  , emptyModeTheory
  , checkWellFormed
  )
import Strat.Poly.TypeExpr
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Attr
import Strat.Poly.Diagram (Diagram(..), genDWithAttrs, diagramDom, diagramCod)
import Strat.Poly.Graph (Edge(..), EdgePayload(..), BinderArg(..), BinderMetaVar(..), canonDiagramRaw, diagramPortIds)
import Strat.Poly.DiagramIso (diagramIsoEq)
import Strat.Poly.Cell2 (Cell2(..))
import Strat.Poly.Traversal (traverseDiagram)
import Strat.Poly.TermExpr (TermExpr(..))
import Strat.Poly.TypeNormalize (termExprToDiagramChecked)
import qualified Strat.Poly.DSL.AST as PolyAST


data PolyPushoutResult = PolyPushoutResult
  { poDoctrine :: Doctrine
  , poInl :: Morphism
  , poInr :: Morphism
  , poGlue :: Morphism
  } deriving (Eq, Show)

type TypeRenameMap = M.Map TypeRef TypeRef
type TypePermMap = M.Map TypeRef [Int]
type AttrSortRenameMap = M.Map AttrSort AttrSort
type GenRenameMap = M.Map (ModeName, GenName) GenName
type CellRenameMap = M.Map (ModeName, Text) Text
type OblRenameMap = M.Map Text Text
type TransformRenameMap = M.Map ModTransformName ModTransformName

data ModePushout = ModePushout
  { mpoModeTheory :: ModeTheory
  , mpoInlModeRen :: M.Map ModeName ModeName
  , mpoInrModeRen :: M.Map ModeName ModeName
  , mpoInlModRen :: M.Map ModName ModName
  , mpoInrModRen :: M.Map ModName ModName
  }
  deriving (Eq, Show)

computePolyPushout :: Text -> Morphism -> Morphism -> Either Text PolyPushoutResult
computePolyPushout name f g = do
  ensureSameSource
  modePushout <- pushoutModeTheoryPreferRight (sanitizePrefix name <> "_pushout") f g
  attrSortMapF <- requireAttrSortRenameMap f
  attrSortMapG <- requireAttrSortRenameMap g
  (typeMapF, permMapF) <- requireTypeRenameMap f
  (typeMapG, permMapG) <- requireTypeRenameMap g
  genMapF <- requireGenRenameMap f
  genMapG <- requireGenRenameMap g
  ensureInjective "attrsort" (M.elems attrSortMapF)
  ensureInjective "attrsort" (M.elems attrSortMapG)
  ensureInjective "type" (M.elems typeMapF)
  ensureInjective "type" (M.elems typeMapG)
  ensureInjective "gen" (M.elems genMapF)
  ensureInjective "gen" (M.elems genMapG)
  let renameAttrSortsB0 = M.fromList [ (img, src) | (src, img) <- M.toList attrSortMapF ]
  let renameAttrSortsC0 = M.fromList [ (img, src) | (src, img) <- M.toList attrSortMapG ]
  let renameTypesB0 = M.fromList [ (img, src) | (src, img) <- M.toList typeMapF ]
  let renameTypesC0 = M.fromList [ (img, src) | (src, img) <- M.toList typeMapG ]
  let permTypesB0 = permMapF
  let permTypesC0 = permMapG
  let renameGensB0 = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList genMapF ]
  let renameGensC0 = M.fromList [ ((m, img), src) | ((m, src), img) <- M.toList genMapG ]
  let prefixB = sanitizePrefix (dName (morTgt f)) <> "_inl"
  let prefixC = sanitizePrefix (dName (morTgt g)) <> "_inr"
  let renameAttrSortsB = M.union renameAttrSortsB0 (disjointAttrSortRenames prefixB (morSrc f) renameAttrSortsB0 (morTgt f))
  let renameAttrSortsC = M.union renameAttrSortsC0 (disjointAttrSortRenames prefixC (morSrc f) renameAttrSortsC0 (morTgt g))
  let renameTypesB = M.union renameTypesB0 (disjointTypeRenames prefixB (morSrc f) renameTypesB0 (morTgt f))
  let renameTypesC = M.union renameTypesC0 (disjointTypeRenames prefixC (morSrc f) renameTypesC0 (morTgt g))
  let renameGensB = M.union renameGensB0 (disjointGenRenames prefixB (morSrc f) renameGensB0 (morTgt f))
  let renameGensC = M.union renameGensC0 (disjointGenRenames prefixC (morSrc f) renameGensC0 (morTgt g))
  let renameCellsB = disjointCellRenames prefixB (morSrc f) (morTgt f)
  let renameCellsC = disjointCellRenames prefixC (morSrc f) (morTgt g)
  let renameOblsB = disjointObligationRenames prefixB (morSrc f) (morTgt f)
  let renameOblsC = disjointObligationRenames prefixC (morSrc f) (morTgt g)
  let renameTransformsB = disjointTransformRenames prefixB (morSrc f) (morTgt f)
  let renameTransformsC = disjointTransformRenames prefixC (morSrc f) (morTgt g)
  b' <-
    renameDoctrine
      (mpoInlModeRen modePushout)
      (mpoInlModRen modePushout)
      renameAttrSortsB
      renameTypesB
      permTypesB0
      renameGensB
      renameCellsB
      renameOblsB
      renameTransformsB
      (morTgt f)
  c' <-
    renameDoctrine
      (mpoInrModeRen modePushout)
      (mpoInrModRen modePushout)
      renameAttrSortsC
      renameTypesC
      permTypesC0
      renameGensC
      renameCellsC
      renameOblsC
      renameTransformsC
      (morTgt g)
  let b'' = b' { dModes = mpoModeTheory modePushout }
  let c'' = c' { dModes = mpoModeTheory modePushout }
  merged <- mergeDoctrineList (mpoModeTheory modePushout) [b'', c'']
  let pres = merged { dName = name }
  let glue =
        g
          { morName = name <> ".glue"
          , morTgt = pres
          , morIsCoercion = True
          }
  inl <-
    buildInj
      (name <> ".inl")
      (morTgt f)
      pres
      (mpoInlModeRen modePushout)
      (mpoInlModRen modePushout)
      renameAttrSortsB
      renameTypesB
      permTypesB0
      renameGensB
  inr <-
    buildInj
      (name <> ".inr")
      (morTgt g)
      pres
      (mpoInrModeRen modePushout)
      (mpoInrModRen modePushout)
      renameAttrSortsC
      renameTypesC
      permTypesC0
      renameGensC
  checkGenerated "inl" inl
  checkGenerated "inr" inr
  pure PolyPushoutResult { poDoctrine = pres, poInl = inl, poInr = inr, poGlue = glue }
  where
    ensureSameSource =
      if morSrc f == morSrc g
        then Right ()
        else Left "poly pushout requires morphisms with the same source"

mkInclusionMorphism :: Text -> Doctrine -> Doctrine -> Either Text Morphism
mkInclusionMorphism name src tgt = do
  mor <- buildInj name src tgt M.empty M.empty M.empty M.empty M.empty M.empty
  checkGenerated "inclusion" mor
  pure mor

computePolyPushoutPreferRight :: Text -> Text -> Morphism -> Morphism -> Either Text PolyPushoutResult
computePolyPushoutPreferRight newName leftPrefix incl impl = do
  ensureSameSource
  let src = morSrc incl
  let body = morTgt incl
  let target = morTgt impl
  modePushout <- pushoutModeTheoryPreferRight leftPrefix incl impl
  attrMapIncl <- requireAttrSortRenameMap incl
  attrMapImpl <- requireAttrSortRenameMap impl
  (typeMapIncl, permMapIncl) <- requireTypeRenameMap incl
  (typeMapImpl, permMapImpl) <- requireTypeRenameMap impl
  genMapIncl <- requireGenRenameMap incl
  genMapImpl <- requireGenRenameMap impl
  ensureInjective "attrsort" (M.elems attrMapIncl)
  ensureInjective "attrsort" (M.elems attrMapImpl)
  ensureInjective "type" (M.elems typeMapIncl)
  ensureInjective "type" (M.elems typeMapImpl)
  ensureInjective "gen" (M.elems genMapIncl)
  ensureInjective "gen" (M.elems genMapImpl)
  interfaceAttrRen <- mkInterfaceAttrSortRenameMap attrMapIncl attrMapImpl
  (interfaceTypeRen, interfacePermRen) <- mkInterfaceTypeRenameMap src typeMapIncl permMapIncl typeMapImpl permMapImpl
  interfaceGenRen <- mkInterfaceGenRenameMap genMapIncl genMapImpl
  let prefix = sanitizePrefix leftPrefix
  let renameAttrSorts =
        M.union interfaceAttrRen
          (collisionAttrSortRenames prefix interfaceAttrRen target body)
  let renameTypes =
        M.union interfaceTypeRen
          (collisionTypeRenames (mpoInlModeRen modePushout) prefix interfaceTypeRen target body)
  let renameGens =
        M.union interfaceGenRen
          (collisionGenRenames (mpoInlModeRen modePushout) prefix interfaceGenRen target body)
  let renameCells = collisionCellRenames prefix src target body
  let renameObls = collisionObligationRenames prefix src target body
  let renameTransforms = collisionTransformRenames prefix src target body
  body' <-
    renameDoctrine
      (mpoInlModeRen modePushout)
      (mpoInlModRen modePushout)
      renameAttrSorts
      renameTypes
      interfacePermRen
      renameGens
      renameCells
      renameObls
      renameTransforms
      body
  target' <-
    renameDoctrine
      (mpoInrModeRen modePushout)
      (mpoInrModRen modePushout)
      M.empty
      M.empty
      M.empty
      M.empty
      M.empty
      M.empty
      M.empty
      target
  let body'' = body' { dModes = mpoModeTheory modePushout }
  let target'' = target' { dModes = mpoModeTheory modePushout }
  merged <- mergeDoctrine (mpoModeTheory modePushout) target'' body''
  let pres = merged { dName = newName }
  inr <-
    buildInj
      (newName <> ".inr")
      target
      pres
      (mpoInrModeRen modePushout)
      (mpoInrModRen modePushout)
      M.empty
      M.empty
      M.empty
      M.empty
  inl <-
    buildInj
      (newName <> ".inl")
      body
      pres
      (mpoInlModeRen modePushout)
      (mpoInlModRen modePushout)
      renameAttrSorts
      renameTypes
      interfacePermRen
      renameGens
  let glue =
        impl
          { morName = newName <> ".glue"
          , morTgt = pres
          , morIsCoercion = True
          }
  checkGenerated "inl" inl
  checkGenerated "inr" inr
  pure PolyPushoutResult { poDoctrine = pres, poInl = inl, poInr = inr, poGlue = glue }
  where
    ensureSameSource =
      if morSrc incl == morSrc impl
        then Right ()
        else Left "poly apply pushout requires morphisms with the same source"

pushoutModeTheoryPreferRight :: Text -> Morphism -> Morphism -> Either Text ModePushout
pushoutModeTheoryPreferRight prefixRaw leftMor rightMor = do
  let prefix = sanitizePrefix prefixRaw
  let mtSrc = dModes (morSrc leftMor)
  let mtLeft = dModes (morTgt leftMor)
  let mtRight = dModes (morTgt rightMor)
  let rightModes = M.keysSet (mtModes mtRight)
  interfaceModePairs <- mapM interfaceModeImage (M.keys (mtModes mtSrc))
  inlModeRen0 <- foldM addModeConstraint M.empty interfaceModePairs
  (inlModeRen, _usedModes) <- completeModeRenames prefix rightModes inlModeRen0 (M.keys (mtModes mtLeft))
  let inrModeRen = M.fromList [ (m, m) | m <- M.keys (mtModes mtRight) ]

  interfaceModPairs <- mapM interfaceModImage (M.keys (mtDecls mtSrc))
  inlModRenForced <- foldM addModConstraint M.empty interfaceModPairs
  let rightMods = M.keysSet (mtDecls mtRight)
  (inlModRen, _usedMods) <- completeModRenames prefix rightMods inlModRenForced (M.keys (mtDecls mtLeft))
  let inrModRen = M.fromList [ (m, m) | m <- M.keys (mtDecls mtRight) ]

  let modesFinal = buildModesFinal inlModeRen inrModeRen mtLeft mtRight
  declsFromRight <- renamedDeclMap inrModeRen inrModRen mtRight
  declsFromLeft <- renamedDeclMap inlModeRen inlModRen mtLeft
  decls0 <- mergeNamedDecls "mode pushout: conflicting modality declarations" declsFromRight declsFromLeft
  let eqns0 =
        map (renameModEqn inrModeRen inrModRen) (mtEqns mtRight)
          <> map (renameModEqn inlModeRen inlModRen) (mtEqns mtLeft)
  (decls1, glueEqns) <-
    foldM
      (addGlueEqn prefix inlModeRen inlModRen inrModeRen inrModRen)
      (decls0, [])
      (M.keys (mtDecls mtSrc))
  transforms <- mergeTransformsPreferRight prefix inlModeRen inlModRen inrModeRen inrModRen mtLeft mtRight
  let mtOut =
        ModeTheory
          { mtModes = modesFinal
          , mtDecls = decls1
          , mtEqns = eqns0 <> glueEqns
          , mtTransforms = transforms
          }
  _ <- checkWellFormed mtOut
  pure
    ModePushout
      { mpoModeTheory = mtOut
      , mpoInlModeRen = inlModeRen
      , mpoInrModeRen = inrModeRen
      , mpoInlModRen = inlModRen
      , mpoInrModRen = inrModRen
      }
  where
    interfaceModeImage srcMode = do
      leftMode <- lookupModeImage "left" leftMor srcMode
      rightMode <- lookupModeImage "right" rightMor srcMode
      pure (leftMode, rightMode)

    addModeConstraint acc (leftMode, rightMode) =
      case M.lookup leftMode acc of
        Nothing -> Right (M.insert leftMode rightMode acc)
        Just existing
          | existing == rightMode -> Right acc
          | otherwise ->
              Left
                ( "mode pushout: incompatible mode images for "
                    <> renderModeName leftMode
                )

    completeModeRenames pref rightSet forced leftModes =
      foldM step (forced, rightSet `S.union` S.fromList (M.elems forced)) leftModes
      where
        step (ren, used) mode =
          case M.lookup mode ren of
            Just _ -> Right (ren, used)
            Nothing ->
              if mode `S.member` used
                then
                  let (fresh, used') = freshModeName pref mode used
                  in Right (M.insert mode fresh ren, used')
                else
                  Right (M.insert mode mode ren, S.insert mode used)

    interfaceModImage srcMod = do
      leftExpr <- lookupModImage "left" leftMor srcMod
      rightExpr <- lookupModImage "right" rightMor srcMod
      pure (srcMod, leftExpr, rightExpr)

    addModConstraint acc (_srcMod, leftExpr, rightExpr) =
      case (mePath leftExpr, mePath rightExpr) of
        ([leftMod], [rightMod]) ->
          case M.lookup leftMod acc of
            Nothing -> Right (M.insert leftMod rightMod acc)
            Just existing
              | existing == rightMod -> Right acc
              | otherwise ->
                  Left
                    ( "mode pushout: incompatible modality images for "
                        <> renderModName leftMod
                    )
        _ -> Right acc

    completeModRenames pref rightSet forced leftMods =
      foldM step (forced, rightSet `S.union` S.fromList (M.elems forced)) leftMods
      where
        step (ren, used) modName =
          case M.lookup modName ren of
            Just _ -> Right (ren, used)
            Nothing ->
              if modName `S.member` used
                then
                  let (fresh, used') = freshModName pref modName used
                  in Right (M.insert modName fresh ren, used')
                else
                  Right (M.insert modName modName ren, S.insert modName used)

    buildModesFinal inlRen inrRen leftMt rightMt =
      let rightModes =
            M.fromList
              [ (renameModeName inrRen mode, ModeInfo { miName = renameModeName inrRen mode })
              | mode <- M.keys (mtModes rightMt)
              ]
      in foldl addLeft rightModes (M.keys (mtModes leftMt))
      where
        addLeft mp mode =
          let mode' = renameModeName inlRen mode
          in M.insertWith (\_ old -> old) mode' (ModeInfo { miName = mode' }) mp

    renamedDeclMap modeRen modRen mt =
      pure
        ( M.fromList
            [ (name', renameDecl modeRen modRen decl)
            | (name, decl) <- M.toList (mtDecls mt)
            , let name' = renameModName modRen name
            ]
        )

    mergeNamedDecls errMsg leftDecls rightDecls =
      foldM step leftDecls (M.toList rightDecls)
      where
        step acc (name, decl) =
          case M.lookup name acc of
            Nothing -> Right (M.insert name decl acc)
            Just existing
              | existing == decl -> Right acc
              | otherwise -> Left errMsg

    addGlueEqn pref inlModeRen' inlModRen' inrModeRen' inrModRen' (decls, eqns) srcMod = do
      leftExpr0 <- lookupModImage "left" leftMor srcMod
      rightExpr0 <- lookupModImage "right" rightMor srcMod
      let leftExpr = renameModExpr inlModeRen' inlModRen' leftExpr0
      let rightExpr = renameModExpr inrModeRen' inrModRen' rightExpr0
      if meSrc leftExpr /= meSrc rightExpr || meTgt leftExpr /= meTgt rightExpr
        then Left "mode pushout: interface modality images have mismatched endpoints"
        else
          case (mePath leftExpr, mePath rightExpr) of
            (pL, pR) | pL == pR -> Right (decls, eqns)
            ([], []) -> Right (decls, eqns)
            ([], _) ->
              Right (decls, eqns <> [ModEqn rightExpr (identityExpr leftExpr)])
            (_, []) ->
              Right (decls, eqns <> [ModEqn leftExpr (identityExpr leftExpr)])
            ([_], [_]) ->
              Left "mode pushout: single-generator modality images should be unified by renaming"
            ([_], _) ->
              Right (decls, eqns <> [ModEqn rightExpr leftExpr])
            (_, [_]) ->
              Right (decls, eqns <> [ModEqn leftExpr rightExpr])
            _ -> do
              let base = ModName (renderModName srcMod)
              let used = S.fromList (M.keys decls)
              let (fresh, _) = freshModName pref base used
              let repExpr =
                    ModExpr
                      { meSrc = meSrc leftExpr
                      , meTgt = meTgt leftExpr
                      , mePath = [fresh]
                      }
              let repDecl =
                    ModDecl
                      { mdName = fresh
                      , mdSrc = meSrc leftExpr
                      , mdTgt = meTgt leftExpr
                      }
              let decls' = M.insert fresh repDecl decls
              Right (decls', eqns <> [ModEqn leftExpr repExpr, ModEqn rightExpr repExpr])


mergeTransformsPreferRight
  :: Text
  -> M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> ModeTheory
  -> ModeTheory
  -> Either Text (M.Map ModTransformName ModTransformDecl)
mergeTransformsPreferRight prefix inlModeRen inlModRen inrModeRen inrModRen leftMt rightMt = do
  let rightRenamed =
        M.fromList
          [ (name, renameTransform inrModeRen inrModRen decl)
          | (name, decl) <- M.toList (mtTransforms rightMt)
          ]
  foldM addLeft rightRenamed (M.toList (mtTransforms leftMt))
  where
    addLeft acc (name, decl) =
      let decl0 = renameTransform inlModeRen inlModRen decl
          used = S.fromList (M.keys acc)
          (name', _) =
            if name `S.member` used
              then freshTransformName prefix name used
              else (name, used)
          decl' = decl0 { mtdName = name' }
      in case M.lookup name' acc of
          Nothing -> Right (M.insert name' decl' acc)
          Just existing
            | existing == decl' -> Right acc
            | otherwise -> Left "mode pushout: conflicting modality transforms"

lookupModeImage :: Text -> Morphism -> ModeName -> Either Text ModeName
lookupModeImage side mor srcMode =
  case M.lookup srcMode (morModeMap mor) of
    Nothing -> Left ("mode pushout: missing " <> side <> " mode mapping")
    Just out -> Right out

lookupModImage :: Text -> Morphism -> ModName -> Either Text ModExpr
lookupModImage side mor srcMod =
  case M.lookup srcMod (morModMap mor) of
    Nothing -> Left ("mode pushout: missing " <> side <> " modality mapping")
    Just out -> Right out

renameModeName :: M.Map ModeName ModeName -> ModeName -> ModeName
renameModeName ren mode = M.findWithDefault mode mode ren

renameModName :: M.Map ModName ModName -> ModName -> ModName
renameModName ren modName = M.findWithDefault modName modName ren

renameModExpr :: M.Map ModeName ModeName -> M.Map ModName ModName -> ModExpr -> ModExpr
renameModExpr modeRen modRen me =
  me
    { meSrc = renameModeName modeRen (meSrc me)
    , meTgt = renameModeName modeRen (meTgt me)
    , mePath = map (renameModName modRen) (mePath me)
    }

renameModEqn :: M.Map ModeName ModeName -> M.Map ModName ModName -> ModEqn -> ModEqn
renameModEqn modeRen modRen (ModEqn lhs rhs) =
  ModEqn
    { meLHS = renameModExpr modeRen modRen lhs
    , meRHS = renameModExpr modeRen modRen rhs
    }

renameDecl :: M.Map ModeName ModeName -> M.Map ModName ModName -> ModDecl -> ModDecl
renameDecl modeRen modRen decl =
  decl
    { mdName = renameModName modRen (mdName decl)
    , mdSrc = renameModeName modeRen (mdSrc decl)
    , mdTgt = renameModeName modeRen (mdTgt decl)
    }

renameTransform :: M.Map ModeName ModeName -> M.Map ModName ModName -> ModTransformDecl -> ModTransformDecl
renameTransform modeRen modRen decl =
  decl
    { mtdFrom = renameModExpr modeRen modRen (mtdFrom decl)
    , mtdTo = renameModExpr modeRen modRen (mtdTo decl)
    }

identityExpr :: ModExpr -> ModExpr
identityExpr me =
  ModExpr
    { meSrc = meSrc me
    , meTgt = meSrc me
    , mePath = []
    }

renderModeName :: ModeName -> Text
renderModeName (ModeName t) = t

renderModName :: ModName -> Text
renderModName (ModName t) = t

computePolyCoproduct :: Text -> Doctrine -> Doctrine -> Either Text PolyPushoutResult
computePolyCoproduct name a b = do
  let empty = Doctrine
        { dName = "Empty"
        , dModes = emptyModeTheory
        , dAcyclicModes = S.empty
        , dAttrSorts = M.empty
        , dTypes = M.empty
        , dGens = M.empty
        , dCells2 = []
      , dActions = M.empty
      , dObligations = []
        }
  let morA = Morphism
        { morName = "coproduct.inl0"
        , morSrc = empty
        , morTgt = a
        , morIsCoercion = True
        , morModeMap = M.empty
        , morModMap = M.empty
        , morAttrSortMap = M.empty
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        }
  let morB = Morphism
        { morName = "coproduct.inr0"
        , morSrc = empty
        , morTgt = b
        , morIsCoercion = True
        , morModeMap = M.empty
        , morModMap = M.empty
        , morAttrSortMap = M.empty
        , morTypeMap = M.empty
        , morGenMap = M.empty
        , morCheck = CheckAll
        , morPolicy = UseAllOriented
        }
  computePolyPushout name morA morB

requireTypeRenameMap :: Morphism -> Either Text (TypeRenameMap, TypePermMap)
requireTypeRenameMap mor = do
  let src = morSrc mor
  let types = allTypes src
  entries <- mapM (typeImage mor) types
  let typeMap = M.fromList [ (srcRef, tgtRef) | (srcRef, tgtRef, _) <- entries ]
  permMap <- foldM insertPerm M.empty entries
  pure (typeMap, permMap)
  where
    typeImage m (srcRef, sig) = do
      (tgtRef, mPerm) <- case M.lookup srcRef (morTypeMap m) of
        Nothing -> Right (srcRef, Nothing)
        Just tmpl -> templateTarget tmpl (tsParams sig)
      ensureTypeExists (morTgt m) tgtRef (length (tsParams sig))
      pure (srcRef, tgtRef, mPerm)
    insertPerm mp (_srcRef, tgtRef, mPerm) =
      case mPerm of
        Nothing -> Right mp
        Just perm ->
          case M.lookup tgtRef mp of
            Nothing -> Right (M.insert tgtRef perm mp)
            Just existing
              | existing == perm -> Right mp
              | otherwise -> Left "poly pushout: inconsistent type permutation"
    templateTarget tmpl srcParams =
      case ttBody tmpl of
        TCon tgtRef args
          | length (ttParams tmpl) == arity
          , length args == arity
          , positionalKindMatch (zip srcParams (ttParams tmpl))
          , let positions = map (argParamIndex (ttParams tmpl)) args
          , all isJust positions
          , let perm = [ i | Just i <- positions ]
          , length perm == S.size (S.fromList perm)
          -> do
            inv <- invertPermutation arity perm
            let ident = [0 .. arity - 1]
            let inv' = if perm == ident then Nothing else Just inv
            pure (tgtRef, inv')
        _ -> Left "poly pushout requires renaming type maps"
      where
        arity = length srcParams

    positionalKindMatch [] = True
    positionalKindMatch ((srcParam, tmplParam):rest) =
      kindMatch srcParam tmplParam && positionalKindMatch rest

    kindMatch srcParam tmplParam =
      case (srcParam, tmplParam) of
        (PS_Ty _, TPType _) -> True
        (PS_Tm _, TPTm _) -> True
        _ -> False

    argParamIndex params arg =
      case arg of
        TAType (TVar v) ->
          findParamIndex params (\p -> case p of TPType v' -> v' == v; _ -> False)
        TATm tm ->
          case termMetaOnly tm of
            Just v ->
              findParamIndex params (\p -> case p of TPTm v' -> v' == v; _ -> False)
            Nothing -> Nothing
        _ -> Nothing

    termMetaOnly (TermDiagram diag) =
      case (IM.elems (dEdges diag), dIn diag, dOut diag) of
        ([edge], [], [outBoundary]) ->
          case (ePayload edge, eIns edge, eOuts edge) of
            (PTmMeta v, [], [outPid]) | outPid == outBoundary -> Just v
            _ -> Nothing
        _ -> Nothing

    findParamIndex params p =
      case [ i | (i, param) <- zip [0 :: Int ..] params, p param ] of
        [i] -> Just i
        _ -> Nothing

    isJust mv =
      case mv of
        Just _ -> True
        Nothing -> False

requireAttrSortRenameMap :: Morphism -> Either Text AttrSortRenameMap
requireAttrSortRenameMap mor = do
  let srcSorts = M.keys (dAttrSorts (morSrc mor))
  let tgtSorts = dAttrSorts (morTgt mor)
  let mapOne srcSort =
        case M.lookup srcSort (morAttrSortMap mor) of
          Nothing ->
            if M.member srcSort tgtSorts
              then Right (srcSort, srcSort)
              else Left "poly pushout: target attrsort missing for implicit identity mapping"
          Just tgtSort ->
            if M.member tgtSort tgtSorts
              then Right (srcSort, tgtSort)
              else Left "poly pushout: target attrsort missing"
  pairs <- mapM mapOne srcSorts
  pure (M.fromList pairs)

invertPermutation :: Int -> [Int] -> Either Text [Int]
invertPermutation n perm
  | length perm /= n = Left "poly pushout: type permutation arity mismatch"
  | any outOfRange perm = Left "poly pushout: type permutation position out of range"
  | length (S.fromList perm) /= n = Left "poly pushout: type permutation is not a bijection"
  | otherwise =
      let mp = IM.fromList (zip perm [0..])
      in Right [ mp IM.! i | i <- [0..n-1] ]
  where
    outOfRange i = i < 0 || i >= n

requireGenRenameMap :: Morphism -> Either Text (M.Map (ModeName, GenName) GenName)
requireGenRenameMap mor = do
  let src = morSrc mor
  let gens = allGens src
  fmap M.fromList (mapM (genImage mor) gens)
  where
    genImage m (mode, gen) = do
      img <- case M.lookup (mode, gdName gen) (morGenMap m) of
        Nothing -> Left "poly pushout requires explicit generator mappings"
        Just d -> do
          imgName <- singleGenName m gen d
          ensureGenExists (morTgt m) mode imgName
          Right imgName
      pure ((mode, gdName gen), img)

singleGenName :: Morphism -> GenDecl -> GenImage -> Either Text GenName
singleGenName mor srcGen image0 = do
  binderSlotsTgt <- mapM (applyMorphismBinderSig mor) binderSlotsSrc
  let expectedBinderSigs = M.fromList (zip holes binderSlotsTgt)
  if giBinderSigs image0 == expectedBinderSigs
    then Right ()
    else Left "poly pushout requires generator mappings to preserve binder-hole signatures"
  canon <- canonDiagramRaw (giDiagram image0)
  case IM.elems (dEdges canon) of
    [edge] -> do
      let boundary = dIn canon <> dOut canon
      let edgePorts = eIns edge <> eOuts edge
      let allPorts = diagramPortIds canon
      expectedAttrs <- expectedAttrMap mor srcGen
      case ePayload edge of
        PGen g attrs bargs ->
          if boundary == edgePorts && length allPorts == length boundary && bargs == expectedBargs && attrs == expectedAttrs
            then Right g
            else Left "poly pushout requires generator mappings to be a single generator"
        _ -> Left "poly pushout requires generator mappings to be a single generator"
    _ -> Left "poly pushout requires generator mappings to be a single generator"
  where
    binderSlotsSrc = [ bs | InBinder bs <- gdDom srcGen ]
    holes = [ BinderMetaVar ("b" <> T.pack (show i)) | i <- [0 .. length binderSlotsSrc - 1] ]
    expectedBargs = map BAMeta holes
    expectedAttrMap m gen = fmap M.fromList (mapM toField (gdAttrs gen))
      where
        toField (fieldName, srcSort) = do
          tgtSort <-
            case M.lookup srcSort (morAttrSortMap m) of
              Nothing -> Left "poly pushout: missing attrsort mapping in generator image"
              Just s -> Right s
          Right (fieldName, ATVar (AttrVar fieldName tgtSort))

ensureTypeExists :: Doctrine -> TypeRef -> Int -> Either Text ()
ensureTypeExists doc ref arity =
  case lookupTypeSig doc ref of
    Left _ -> Left "poly pushout: target type missing"
    Right sig
      | length (tsParams sig) == arity -> Right ()
      | otherwise -> Left "poly pushout: target type arity mismatch"

ensureGenExists :: Doctrine -> ModeName -> GenName -> Either Text ()
ensureGenExists doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing -> Left "poly pushout: target generator missing"
    Just _ -> Right ()

ensureInjective :: Ord a => Text -> [a] -> Either Text ()
ensureInjective label images =
  case firstDup images of
    Nothing -> Right ()
    Just _ -> Left ("poly pushout requires injective " <> label <> " mapping")
  where
    firstDup xs = go S.empty xs
    go _ [] = Nothing
    go seen (x:rest)
      | x `S.member` seen = Just x
      | otherwise = go (S.insert x seen) rest

disjointTypeRenames :: Text -> Doctrine -> TypeRenameMap -> Doctrine -> TypeRenameMap
disjointTypeRenames prefix src interfaceRen tgt =
  foldl add M.empty (M.toList (dTypes tgt))
  where
    srcNames = namesByMode [ (trMode ref, trName ref) | (ref, _) <- allTypes src ]
    add acc (mode, table) =
      let reserved = M.findWithDefault S.empty mode srcNames
          names = M.keys table
          (_, mp) = foldl (step mode) (reserved, M.empty) names
      in M.union acc mp
    step mode (used, mp) name =
      let key = TypeRef mode name
      in if M.member key interfaceRen
        then (used, mp)
        else
          let (name', used') = freshTypeName prefix name used
              key' = TypeRef mode name'
          in (used', M.insert key key' mp)

disjointAttrSortRenames :: Text -> Doctrine -> AttrSortRenameMap -> Doctrine -> AttrSortRenameMap
disjointAttrSortRenames prefix src interfaceRen tgt =
  let reserved = S.fromList (M.keys (dAttrSorts src))
      names = M.keys (dAttrSorts tgt)
      (_, mp) = foldl step (reserved, M.empty) names
  in mp
  where
    step (used, mp) name =
      if M.member name interfaceRen
        then (used, mp)
        else
          let (name', used') = freshAttrSortName prefix name used
          in (used', M.insert name name' mp)

disjointGenRenames :: Text -> Doctrine -> GenRenameMap -> Doctrine -> GenRenameMap
disjointGenRenames prefix src interfaceRen tgt =
  foldl add M.empty (M.toList (dGens tgt))
  where
    srcNames = namesByMode [ (mode, gdName gen) | (mode, gen) <- allGens src ]
    add acc (mode, table) =
      let reserved = M.findWithDefault S.empty mode srcNames
          names = map gdName (M.elems table)
          (_, mp) = foldl (step mode) (reserved, M.empty) names
      in M.union acc mp
    step mode (used, mp) name =
      let key = (mode, name)
      in if M.member key interfaceRen
        then (used, mp)
        else
          let (name', used') = freshGenName prefix name used
          in (used', M.insert key name' mp)

disjointCellRenames :: Text -> Doctrine -> Doctrine -> CellRenameMap
disjointCellRenames prefix src tgt =
  snd (foldl step (srcNames, M.empty) (dCells2 tgt))
  where
    srcNames = namesByMode [ (dMode (c2LHS cell), c2Name cell) | cell <- dCells2 src ]
    step (usedByMode, mp) cell =
      let mode = dMode (c2LHS cell)
          name = c2Name cell
          used = M.findWithDefault S.empty mode usedByMode
      in if name `S.member` used
        then (usedByMode, mp)
        else
          let (name', used') = freshCellName prefix name used
              usedByMode' = M.insert mode used' usedByMode
          in (usedByMode', M.insert (mode, name) name' mp)

disjointObligationRenames :: Text -> Doctrine -> Doctrine -> OblRenameMap
disjointObligationRenames prefix src tgt =
  snd (foldl step (srcNames, M.empty) (dObligations tgt))
  where
    srcNames = S.fromList (map obName (dObligations src))
    step (used, mp) obl =
      let name = obName obl
      in if name `S.member` used
        then (used, mp)
        else
          let (name', used') = freshCellName prefix name used
          in (used', M.insert name name' mp)

disjointTransformRenames :: Text -> Doctrine -> Doctrine -> TransformRenameMap
disjointTransformRenames prefix src tgt =
  snd (foldl step (srcNames, M.empty) (M.keys (mtTransforms (dModes tgt))))
  where
    srcNames = S.fromList (M.keys (mtTransforms (dModes src)))
    step (used, mp) name =
      if name `S.member` used
        then (used, mp)
        else
          let (name', used') = freshTransformName prefix name used
          in (used', M.insert name name' mp)

mkInterfaceAttrSortRenameMap :: AttrSortRenameMap -> AttrSortRenameMap -> Either Text AttrSortRenameMap
mkInterfaceAttrSortRenameMap leftMap rightMap =
  foldM add M.empty (M.toList leftMap)
  where
    add acc (srcSort, imgLeft) = do
      imgRight <-
        case M.lookup srcSort rightMap of
          Nothing -> Left "apply pushout: missing interface attrsort mapping on right morphism"
          Just out -> Right out
      case M.lookup imgLeft acc of
        Nothing -> Right (M.insert imgLeft imgRight acc)
        Just existing
          | existing == imgRight -> Right acc
          | otherwise -> Left "apply pushout: inconsistent attrsort interface images"

mkInterfaceTypeRenameMap
  :: Doctrine
  -> TypeRenameMap
  -> TypePermMap
  -> TypeRenameMap
  -> TypePermMap
  -> Either Text (TypeRenameMap, TypePermMap)
mkInterfaceTypeRenameMap src leftMap leftPerm rightMap rightPerm = do
  foldM add (M.empty, M.empty) (allTypes src)
  where
    add (renAcc, permAcc) (srcRef, sig) = do
      imgLeft <-
        case M.lookup srcRef leftMap of
          Nothing -> Left "apply pushout: missing interface type mapping on left morphism"
          Just out -> Right out
      imgRight <-
        case M.lookup srcRef rightMap of
          Nothing -> Left "apply pushout: missing interface type mapping on right morphism"
          Just out -> Right out
      renAcc' <-
        case M.lookup imgLeft renAcc of
          Nothing -> Right (M.insert imgLeft imgRight renAcc)
          Just existing
            | existing == imgRight -> Right renAcc
            | otherwise -> Left "apply pushout: inconsistent type interface images"
      let arity = length (tsParams sig)
      invLeft <- normalizeInvPerm arity (M.lookup imgLeft leftPerm)
      invRight <- normalizeInvPerm arity (M.lookup imgRight rightPerm)
      rightPermFwd <- invertPermutation arity invRight
      let perm = [ invLeft !! i | i <- rightPermFwd ]
      let ident = [0 .. arity - 1]
      permAcc' <-
        if perm == ident
          then Right permAcc
          else
            case M.lookup imgLeft permAcc of
              Nothing -> Right (M.insert imgLeft perm permAcc)
              Just existing
                | existing == perm -> Right permAcc
                | otherwise -> Left "apply pushout: inconsistent type interface permutations"
      pure (renAcc', permAcc')

    normalizeInvPerm n mPerm =
      case mPerm of
        Nothing -> Right [0 .. n - 1]
        Just perm -> do
          if length perm == n
            then Right perm
            else Left "apply pushout: interface permutation arity mismatch"

mkInterfaceGenRenameMap
  :: M.Map (ModeName, GenName) GenName
  -> M.Map (ModeName, GenName) GenName
  -> Either Text (M.Map (ModeName, GenName) GenName)
mkInterfaceGenRenameMap leftMap rightMap =
  foldM add M.empty (M.toList leftMap)
  where
    add acc (srcKey, imgLeft) = do
      imgRight <-
        case M.lookup srcKey rightMap of
          Nothing -> Left "apply pushout: missing interface generator mapping on right morphism"
          Just out -> Right out
      let outKey = (fst srcKey, imgLeft)
      case M.lookup outKey acc of
        Nothing -> Right (M.insert outKey imgRight acc)
        Just existing
          | existing == imgRight -> Right acc
          | otherwise -> Left "apply pushout: inconsistent generator interface images"

collisionTypeRenames :: M.Map ModeName ModeName -> Text -> TypeRenameMap -> Doctrine -> Doctrine -> TypeRenameMap
collisionTypeRenames modeRen prefix interfaceRen target body =
  foldl addByMode M.empty (M.toList (dTypes body))
  where
    targetNames =
      namesByMode
        [ (mode, name)
        | (mode, table) <- M.toList (dTypes target)
        , name <- M.keys table
        ]
    interfaceTargets =
      namesByMode
        [ (trMode ref, trName ref)
        | ref <- M.elems interfaceRen
        ]
    addByMode acc (mode, table) =
      let mode' = renameModeName modeRen mode
          used0 = S.union (M.findWithDefault S.empty mode' targetNames) (M.findWithDefault S.empty mode' interfaceTargets)
          (renMode, _used) = foldl (step mode) (M.empty, used0) (M.keys table)
      in M.union acc renMode
    step mode (renAcc, used) name =
      let key = TypeRef mode name
      in if M.member key interfaceRen
        then (renAcc, used)
        else
          if name `S.member` used
            then
              let (fresh, used') = freshTypeName prefix name used
              in (M.insert key (TypeRef mode fresh) renAcc, used')
            else (renAcc, S.insert name used)

collisionAttrSortRenames :: Text -> AttrSortRenameMap -> Doctrine -> Doctrine -> AttrSortRenameMap
collisionAttrSortRenames prefix interfaceRen target body =
  fst (foldl step (M.empty, used0) (M.keys (dAttrSorts body)))
  where
    used0 = S.union (S.fromList (M.keys (dAttrSorts target))) (S.fromList (M.elems interfaceRen))
    step (renAcc, used) name =
      if M.member name interfaceRen
        then (renAcc, used)
        else
          if name `S.member` used
            then
              let (fresh, used') = freshAttrSortName prefix name used
              in (M.insert name fresh renAcc, used')
            else (renAcc, S.insert name used)

collisionGenRenames
  :: M.Map ModeName ModeName
  -> Text
  -> M.Map (ModeName, GenName) GenName
  -> Doctrine
  -> Doctrine
  -> M.Map (ModeName, GenName) GenName
collisionGenRenames modeRen prefix interfaceRen target body =
  foldl addByMode M.empty (M.toList (dGens body))
  where
    targetNames =
      namesByMode
        [ (mode, gdName gen)
        | (mode, table) <- M.toList (dGens target)
        , gen <- M.elems table
        ]
    interfaceTargets =
      namesByMode
        [ (mode, name)
        | ((mode, _), name) <- M.toList interfaceRen
        ]
    addByMode acc (mode, table) =
      let mode' = renameModeName modeRen mode
          used0 = S.union (M.findWithDefault S.empty mode' targetNames) (M.findWithDefault S.empty mode' interfaceTargets)
          names = map gdName (M.elems table)
          (renMode, _used) = foldl (step mode) (M.empty, used0) names
      in M.union acc renMode
    step mode (renAcc, used) name =
      let key = (mode, name)
      in if M.member key interfaceRen
        then (renAcc, used)
        else
          if name `S.member` used
            then
              let (fresh, used') = freshGenName prefix name used
              in (M.insert key fresh renAcc, used')
            else (renAcc, S.insert name used)

collisionCellRenames :: Text -> Doctrine -> Doctrine -> Doctrine -> M.Map (ModeName, Text) Text
collisionCellRenames prefix src target body =
  fst (foldl step (M.empty, used0) (dCells2 body))
  where
    srcNames =
      namesByMode
        [ (dMode (c2LHS cell), c2Name cell)
        | cell <- dCells2 src
        ]
    used0 =
      namesByMode
        [ (dMode (c2LHS cell), c2Name cell)
        | cell <- dCells2 target
        ]
    step (renAcc, usedByMode) cell =
      let mode = dMode (c2LHS cell)
          name = c2Name cell
          used = M.findWithDefault S.empty mode usedByMode
          isInterface = name `S.member` M.findWithDefault S.empty mode srcNames
      in if isInterface
        then (renAcc, M.insert mode (S.insert name used) usedByMode)
        else
          if name `S.member` used
            then
              let (fresh, used') = freshCellName prefix name used
                  usedByMode' = M.insert mode used' usedByMode
              in (M.insert (mode, name) fresh renAcc, usedByMode')
            else
              let usedByMode' = M.insert mode (S.insert name used) usedByMode
              in (renAcc, usedByMode')

collisionObligationRenames :: Text -> Doctrine -> Doctrine -> Doctrine -> OblRenameMap
collisionObligationRenames prefix src target body =
  fst (foldl step (M.empty, used0) (dObligations body))
  where
    interfaceNames = S.fromList (map obName (dObligations src))
    used0 = S.fromList (map obName (dObligations target))
    step (renAcc, used) obl =
      let name = obName obl
          isInterface = name `S.member` interfaceNames
      in if isInterface
        then (renAcc, S.insert name used)
        else
          if name `S.member` used
            then
              let (fresh, used') = freshCellName prefix name used
              in (M.insert name fresh renAcc, used')
            else (renAcc, S.insert name used)

collisionTransformRenames :: Text -> Doctrine -> Doctrine -> Doctrine -> TransformRenameMap
collisionTransformRenames prefix src target body =
  fst (foldl step (M.empty, used0) (M.keys (mtTransforms (dModes body))))
  where
    interfaceNames = S.fromList (M.keys (mtTransforms (dModes src)))
    used0 = S.fromList (M.keys (mtTransforms (dModes target)))
    step (renAcc, used) name =
      let isInterface = name `S.member` interfaceNames
      in if isInterface
        then (renAcc, S.insert name used)
        else
          if name `S.member` used
            then
              let (fresh, used') = freshTransformName prefix name used
              in (M.insert name fresh renAcc, used')
            else (renAcc, S.insert name used)

namesByMode :: (Ord a) => [(ModeName, a)] -> M.Map ModeName (S.Set a)
namesByMode pairs =
  foldl add M.empty pairs
  where
    add mp (mode, name) =
      let set = M.findWithDefault S.empty mode mp
      in M.insert mode (S.insert name set) mp

sanitizePrefix :: Text -> Text
sanitizePrefix = T.map (\c -> if c == '.' then '_' else c)

freshTypeName :: Text -> TypeName -> S.Set TypeName -> (TypeName, S.Set TypeName)
freshTypeName prefix (TypeName base) used =
  let baseName = prefix <> "_" <> base
      candidate = TypeName baseName
  in freshen candidate (\n -> TypeName (baseName <> "_" <> T.pack (show n))) used

freshModeName :: Text -> ModeName -> S.Set ModeName -> (ModeName, S.Set ModeName)
freshModeName prefix (ModeName base) used =
  let baseName = prefix <> "_" <> base
      candidate = ModeName baseName
  in freshen candidate (\n -> ModeName (baseName <> "_" <> T.pack (show n))) used

freshModName :: Text -> ModName -> S.Set ModName -> (ModName, S.Set ModName)
freshModName prefix (ModName base) used =
  let baseName = prefix <> "_" <> base
      candidate = ModName baseName
  in freshen candidate (\n -> ModName (baseName <> "_" <> T.pack (show n))) used

freshAttrSortName :: Text -> AttrSort -> S.Set AttrSort -> (AttrSort, S.Set AttrSort)
freshAttrSortName prefix (AttrSort base) used =
  let baseName = prefix <> "_" <> base
      candidate = AttrSort baseName
  in freshen candidate (\n -> AttrSort (baseName <> "_" <> T.pack (show n))) used

freshGenName :: Text -> GenName -> S.Set GenName -> (GenName, S.Set GenName)
freshGenName prefix (GenName base) used =
  let baseName = prefix <> "_" <> base
      candidate = GenName baseName
  in freshen candidate (\n -> GenName (baseName <> "_" <> T.pack (show n))) used

freshCellName :: Text -> Text -> S.Set Text -> (Text, S.Set Text)
freshCellName prefix base used =
  let baseName = prefix <> "_" <> base
      candidate = baseName
  in freshen candidate (\n -> baseName <> "_" <> T.pack (show n)) used

freshTransformName :: Text -> ModTransformName -> S.Set ModTransformName -> (ModTransformName, S.Set ModTransformName)
freshTransformName prefix (ModTransformName base) used =
  let baseName = prefix <> "_" <> base
      candidate = ModTransformName baseName
  in freshen candidate (\n -> ModTransformName (baseName <> "_" <> T.pack (show n))) used

freshen :: (Ord a) => a -> (Int -> a) -> S.Set a -> (a, S.Set a)
freshen candidate mk used =
  if candidate `S.member` used
    then go 1
    else (candidate, S.insert candidate used)
  where
    go n =
      let cand = mk n
      in if cand `S.member` used
        then go (n + 1)
        else (cand, S.insert cand used)

renameDoctrine
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> GenRenameMap
  -> CellRenameMap
  -> OblRenameMap
  -> TransformRenameMap
  -> Doctrine
  -> Either Text Doctrine
renameDoctrine modeRen modRen attrRen tyRen permRen genRen cellRen oblRen transformRen doc = do
  modes' <- renameModeTransforms transformRen (dModes doc)
  attrSorts' <- renameAttrSorts attrRen (dAttrSorts doc)
  types' <- renameTypeTables (dTypes doc)
  gens' <- renameGenTables (dGens doc)
  cells' <- mapM (renameCell modeRen modRen attrRen tyRen permRen genRen cellRen) (dCells2 doc)
  actions' <- renameActions (dActions doc)
  obligations' <- mapM renameObligation (dObligations doc)
  let acyclic' =
        S.fromList [ renameModeName modeRen m | m <- S.toList (dAcyclicModes doc) ]
  pure
    doc
      { dModes = modes'
      , dAcyclicModes = acyclic'
      , dAttrSorts = attrSorts'
      , dTypes = types'
      , dGens = gens'
      , dCells2 = cells'
      , dActions = actions'
      , dObligations = obligations'
      }
  where
    mt = dModes doc

    renameModeTransforms transRen mt0 = do
      transforms' <- foldM addTransform M.empty (M.toList (mtTransforms mt0))
      let modes' =
            M.fromList
              [ (mode', info { miName = mode' })
              | (mode, info) <- M.toList (mtModes mt0)
              , let mode' = renameModeName modeRen mode
              ]
      let decls' =
            M.fromList
              [ (name', renameDecl modeRen modRen decl)
              | (name, decl) <- M.toList (mtDecls mt0)
              , let name' = renameModName modRen name
              ]
      let eqns' = map (renameModEqn modeRen modRen) (mtEqns mt0)
      Right mt0 { mtModes = modes', mtDecls = decls', mtEqns = eqns', mtTransforms = transforms' }
      where
        addTransform acc (name, decl) = do
          let name' = M.findWithDefault name name transRen
          let decl0 = renameTransform modeRen modRen decl
          let mode = meTgt (mtdFrom decl0)
          let witness' = M.findWithDefault (mtdWitness decl0) (mode, mtdWitness decl0) genRen
          let decl' = decl0 { mtdName = name', mtdWitness = witness' }
          case M.lookup name' acc of
            Nothing -> Right (M.insert name' decl' acc)
            Just existing
              | existing == decl' -> Right acc
              | otherwise -> Left "poly pushout: modality transform name collision"

    renameAttrSorts ren table =
      foldl add (Right M.empty) (M.elems table)
      where
        add acc decl = do
          mp <- acc
          let name' = M.findWithDefault (asName decl) (asName decl) ren
          let decl' = decl { asName = name' }
          case M.lookup name' mp of
            Nothing -> Right (M.insert name' decl' mp)
            Just existing | existing == decl' -> Right mp
            _ -> Left "poly pushout: attribute sort collision"

    renameTypeTables tables =
      foldM addType M.empty
        [ (mode, name, sig)
        | (mode, table) <- M.toList tables
        , (name, sig) <- M.toList table
        ]
      where
        addType acc (mode, name, sig) = do
          let ref = TypeRef mode name
          sig1 <- renameTypeSig modeRen modRen tyRen permRen sig
          sig2 <-
            case M.lookup ref permRen of
              Nothing -> Right sig1
              Just perm -> do
                params <- applyPerm perm (tsParams sig1)
                Right sig1 { tsParams = params }
          let ref1 = M.findWithDefault ref ref tyRen
          let ref' = ref1 { trMode = renameModeName modeRen (trMode ref1) }
          let table0 = M.findWithDefault M.empty (trMode ref') acc
          case M.lookup (trName ref') table0 of
            Nothing ->
              let table' = M.insert (trName ref') sig2 table0
              in Right (M.insert (trMode ref') table' acc)
            Just existing
              | existing == sig2 -> Right acc
              | otherwise -> Left "poly pushout: type name collision"

    renameGenTables tables =
      foldM addGen M.empty
        [ (mode, gen)
        | (mode, table) <- M.toList tables
        , gen <- M.elems table
        ]
      where
        addGen acc (mode, gen) = do
          let name' = M.findWithDefault (gdName gen) (mode, gdName gen) genRen
          let mode' = renameModeName modeRen mode
          dom' <- mapM (renameInputShape modeRen modRen tyRen permRen) (gdDom gen)
          cod' <- mapM (renameTypeExpr modeRen modRen tyRen permRen) (gdCod gen)
          tyVars' <- mapM renameTyVar (gdTyVars gen)
          tmVars' <- mapM renameTmVar (gdTmVars gen)
          let attrs' = [ (fieldName, M.findWithDefault sortName sortName attrRen) | (fieldName, sortName) <- gdAttrs gen ]
          let gen' =
                gen
                  { gdName = name'
                  , gdMode = mode'
                  , gdTyVars = tyVars'
                  , gdTmVars = tmVars'
                  , gdDom = dom'
                  , gdCod = cod'
                  , gdAttrs = attrs'
                  }
          let table0 = M.findWithDefault M.empty mode' acc
          case M.lookup name' table0 of
            Nothing ->
              let table' = M.insert name' gen' table0
              in Right (M.insert mode' table' acc)
            Just existing | existing == gen' -> Right acc
            _ -> Left "poly pushout: generator name collision"

        renameTyVar tv = Right tv { tvMode = renameModeName modeRen (tvMode tv) }
        renameTmVar tmVar = do
          sort' <- renameTypeExpr modeRen modRen tyRen permRen (tmvSort tmVar)
          Right tmVar { tmvSort = sort' }

    renameActions table =
      foldM addAction M.empty (M.toList table)
      where
        addAction acc (_modName, action) = do
          let modName' = renameModName modRen (maMod action)
          genMap' <- renameActionGenMap (maGenMap action)
          let action' = action { maMod = modName', maGenMap = genMap' }
          case M.lookup modName' acc of
            Nothing -> Right (M.insert modName' action' acc)
            Just existing
              | existing == action' -> Right acc
              | otherwise -> Left "poly pushout: modality action collision"

    renameActionGenMap table =
      foldl add (Right M.empty) (M.toList table)
      where
        add acc ((mode, genName), diag) = do
          mp <- acc
          let mode' = renameModeName modeRen mode
          let genName' = M.findWithDefault genName (mode, genName) genRen
          diag' <- renameDiagram modeRen modRen attrRen tyRen permRen genRen diag
          case M.lookup (mode', genName') mp of
            Nothing -> Right (M.insert (mode', genName') diag' mp)
            Just existing
              | existing == diag' -> Right mp
              | otherwise -> Left "poly pushout: modality action generator collision"

    renameObligation obl = do
      let name' = M.findWithDefault (obName obl) (obName obl) oblRen
      let tyVarNames = S.fromList (map tvName (obTyVars obl))
      let tmVarNames = S.fromList (map tmvName (obTmVars obl))
      let mode' = renameModeName modeRen (obMode obl)
      dom' <- mapM (renameTypeExpr modeRen modRen tyRen permRen) (obDom obl)
      cod' <- mapM (renameTypeExpr modeRen modRen tyRen permRen) (obCod obl)
      lhs' <- renameOblExpr tyVarNames tmVarNames mode' (obLHSExpr obl)
      rhs' <- renameOblExpr tyVarNames tmVarNames mode' (obRHSExpr obl)
      pure
        obl
          { obName = name'
          , obMode = mode'
          , obDom = dom'
          , obCod = cod'
          , obLHSExpr = lhs'
          , obRHSExpr = rhs'
          }

    renameOblExpr tyVarNames tmVarNames mode expr =
      case expr of
        PolyAST.ROEDiag d ->
          PolyAST.ROEDiag <$> renameRawDiagExpr tyVarNames tmVarNames mode d
        PolyAST.ROEMap me inner -> do
          (innerMode, _outerMode) <- rawModExprEndpoints mode me
          inner' <- renameOblExpr tyVarNames tmVarNames innerMode inner
          pure (PolyAST.ROEMap me inner')
        PolyAST.ROEGen ->
          Right PolyAST.ROEGen
        PolyAST.ROELiftDom d ->
          PolyAST.ROELiftDom <$> renameRawDiagExpr tyVarNames tmVarNames mode d
        PolyAST.ROELiftCod d ->
          PolyAST.ROELiftCod <$> renameRawDiagExpr tyVarNames tmVarNames mode d
        PolyAST.ROEComp a b ->
          PolyAST.ROEComp <$> renameOblExpr tyVarNames tmVarNames mode a <*> renameOblExpr tyVarNames tmVarNames mode b
        PolyAST.ROETensor a b ->
          PolyAST.ROETensor <$> renameOblExpr tyVarNames tmVarNames mode a <*> renameOblExpr tyVarNames tmVarNames mode b

    renameRawDiagExpr tyVarNames tmVarNames mode expr =
      case expr of
        PolyAST.RDId ctx ->
          PolyAST.RDId <$> mapM (renameRawTypeAsType tyVarNames tmVarNames mode) ctx
        PolyAST.RDMetaVar name ->
          Right (PolyAST.RDMetaVar name)
        PolyAST.RDGen name mTyArgs mAttrArgs mBinderArgs -> do
          let genName = GenName name
          let genName' = M.findWithDefault genName (mode, genName) genRen
          mTyArgs' <- renameRawGenArgs tyVarNames tmVarNames mode genName mTyArgs
          mBinderArgs' <- mapM (mapM (renameRawBinderArg tyVarNames tmVarNames mode)) mBinderArgs
          pure (PolyAST.RDGen (renderGenName genName') mTyArgs' mAttrArgs mBinderArgs')
        PolyAST.RDTermRef name ->
          Right (PolyAST.RDTermRef name)
        PolyAST.RDSplice name ->
          Right (PolyAST.RDSplice name)
        PolyAST.RDBox name inner ->
          PolyAST.RDBox name <$> renameRawDiagExpr tyVarNames tmVarNames mode inner
        PolyAST.RDLoop inner ->
          PolyAST.RDLoop <$> renameRawDiagExpr tyVarNames tmVarNames mode inner
        PolyAST.RDMap me inner -> do
          (innerMode, _outerMode) <- rawModExprEndpoints mode me
          inner' <- renameRawDiagExpr tyVarNames tmVarNames innerMode inner
          pure (PolyAST.RDMap me inner')
        PolyAST.RDComp a b ->
          PolyAST.RDComp <$> renameRawDiagExpr tyVarNames tmVarNames mode a <*> renameRawDiagExpr tyVarNames tmVarNames mode b
        PolyAST.RDTensor a b ->
          PolyAST.RDTensor <$> renameRawDiagExpr tyVarNames tmVarNames mode a <*> renameRawDiagExpr tyVarNames tmVarNames mode b

    renameRawBinderArg tyVarNames tmVarNames mode barg =
      case barg of
        PolyAST.RBAExpr d ->
          PolyAST.RBAExpr <$> renameRawDiagExpr tyVarNames tmVarNames mode d
        PolyAST.RBAMeta name ->
          Right (PolyAST.RBAMeta name)

    renameRawTypeAsType tyVarNames tmVarNames mode ty =
      case ty of
        PolyAST.RPTVar name ->
          if name `S.member` tyVarNames
            then Right (PolyAST.RPTVar name)
            else do
              ref <- resolveRawTypeRefAsType (PolyAST.RawTypeRef Nothing name)
              let ref0 = M.findWithDefault ref ref tyRen
              let ref' = ref0 { trMode = renameModeName modeRen (trMode ref0) }
              pure (mkQualifiedRawTypeCon ref' [])
        PolyAST.RPTCon ref args ->
          case asModalityCall ref args of
            Just (rawMe, innerRaw) -> do
              (srcMode, _tgtMode) <- rawModExprEndpoints mode rawMe
              inner' <- renameRawTypeAsType tyVarNames tmVarNames srcMode innerRaw
              pure (PolyAST.RPTCon ref [inner'])
            Nothing -> do
              ref0 <- resolveRawTypeRefAsType ref
              sig <- lookupTypeSig doc ref0
              if length (tsParams sig) /= length args
                then Left "poly pushout: obligation raw type arity mismatch"
                else do
                  args0 <- mapM (renameOneArg tyVarNames tmVarNames) (zip (tsParams sig) args)
                  let args1 =
                        case M.lookup ref0 permRen of
                          Nothing -> Right args0
                          Just perm -> applyPerm perm args0
                  args2 <- args1
                  let ref1 = M.findWithDefault ref0 ref0 tyRen
                  let ref' = ref1 { trMode = renameModeName modeRen (trMode ref1) }
                  pure (mkQualifiedRawTypeCon ref' args2)
        PolyAST.RPTMod me inner -> do
          (innerMode, _outerMode) <- rawModExprEndpoints mode me
          inner' <- renameRawTypeAsType tyVarNames tmVarNames innerMode inner
          pure (PolyAST.RPTMod me inner')

    renameRawTypeAsTmTerm tmVarNames mode ty =
      case ty of
        PolyAST.RPTVar name ->
          if name `S.member` tmVarNames
            then Right (PolyAST.RPTVar name)
            else do
              let name' = renameTmFunLike mode name
              Right (PolyAST.RPTVar name')
        PolyAST.RPTCon ref args -> do
          args' <- mapM (renameRawTypeAsTmTerm tmVarNames mode) args
          let name' = renameTmFunLike mode (PolyAST.rtrName ref)
          pure
            ( PolyAST.RPTCon
                ref
                  { PolyAST.rtrName = name'
                  }
                args'
            )
        PolyAST.RPTMod _ _ ->
          Left "poly pushout: modality application is invalid in term-argument context"

    renameRawGenArgs tyVarNames tmVarNames mode genName mArgs =
      case mArgs of
        Nothing -> Right Nothing
        Just args -> do
          genDecl <- lookupGenDecl mode genName
          let paramKinds =
                map Left (gdTyVars genDecl)
                  <> map Right (gdTmVars genDecl)
          if length args > length paramKinds
            then Left "poly pushout: obligation raw generator argument mismatch"
            else do
              args' <- mapM (renameGenArg tyVarNames tmVarNames mode) (zip args (take (length args) paramKinds))
              Right (Just args')

    renameGenArg tyVarNames tmVarNames mode (arg, kind) =
      case kind of
        Left _ ->
          renameRawTypeAsType tyVarNames tmVarNames mode arg
        Right tmv ->
          renameRawTypeAsTmTerm tmVarNames (typeMode (tmvSort tmv)) arg

    renameOneArg tyVarNames tmVarNames (param, arg) =
      case param of
        PS_Ty mode ->
          renameRawTypeAsType tyVarNames tmVarNames mode arg
        PS_Tm sortTy ->
          renameRawTypeAsTmTerm tmVarNames (typeMode sortTy) arg

    lookupGenDecl mode genName =
      case M.lookup mode (dGens doc) >>= M.lookup genName of
        Nothing -> Left "poly pushout: obligation raw diagram references unknown generator"
        Just gd -> Right gd

    resolveRawTypeRefAsType rawRef =
      case PolyAST.rtrMode rawRef of
        Just modeTxt -> do
          let mode = ModeName modeTxt
          let tname = TypeName (PolyAST.rtrName rawRef)
          case M.lookup mode (dTypes doc) >>= M.lookup tname of
            Nothing -> Left "poly pushout: obligation raw type references unknown qualified type"
            Just _ -> Right (TypeRef mode tname)
        Nothing -> do
          let tname = TypeName (PolyAST.rtrName rawRef)
          let modes =
                [ mode
                | (mode, table) <- M.toList (dTypes doc)
                , M.member tname table
                ]
          case modes of
            [] -> Left "poly pushout: obligation raw type references unknown type"
            [mode] -> Right (TypeRef mode tname)
            _ -> Left "poly pushout: obligation raw type is ambiguous (use Mode.Type)"

    asModalityCall rawRef args =
      case (PolyAST.rtrMode rawRef, PolyAST.rtrName rawRef, args) of
        (Nothing, name, [inner]) ->
          if hasModality name
            then Just (PolyAST.RMComp [name], inner)
            else Nothing
        (Just modeTok, name, [inner]) ->
          if hasQualifiedType modeTok name
            then Nothing
            else
              if hasModality modeTok && hasModality name
                then Just (PolyAST.RMComp [modeTok, name], inner)
                else Nothing
        _ -> Nothing

    hasModality tok =
      M.member (ModName tok) (mtDecls mt)

    hasQualifiedType modeTok tyTok =
      let mode = ModeName modeTok
          tname = TypeName tyTok
      in case M.lookup mode (dTypes doc) of
        Nothing -> False
        Just table -> M.member tname table

    renameTmFunLike mode name =
      let genName = GenName name
          genName' = M.findWithDefault genName (mode, genName) genRen
      in renderGenName genName'

    mkQualifiedRawTypeCon ref args =
      PolyAST.RPTCon
        PolyAST.RawTypeRef
          { PolyAST.rtrMode = Just (renderModeName (trMode ref))
          , PolyAST.rtrName = renderTypeName (trName ref)
          }
        args

    rawModExprEndpoints fallbackMode me =
      case me of
        PolyAST.RMId modeNameTxt ->
          let modeName = ModeName modeNameTxt
          in if M.member modeName (mtModes mt)
            then Right (modeName, modeName)
            else Left "poly pushout: obligation raw modality references unknown mode"
        PolyAST.RMComp [] ->
          Right (fallbackMode, fallbackMode)
        PolyAST.RMComp (tok:toks) -> do
          firstDecl <- lookupRawMod tok
          (_cur, out) <- foldM step (mdSrc firstDecl, mdTgt firstDecl) toks
          pure (mdSrc firstDecl, out)
          where
            step (_curIn, curOut) tok' = do
              decl <- lookupRawMod tok'
              if mdSrc decl == curOut
                then Right (curOut, mdTgt decl)
                else Left "poly pushout: obligation raw modality composition type mismatch"

    lookupRawMod tok =
      case M.lookup (ModName tok) (mtDecls mt) of
        Nothing -> Left "poly pushout: obligation raw modality references unknown modality"
        Just decl -> Right decl

    renderModeName (ModeName t) = t
    renderTypeName (TypeName t) = t
    renderGenName (GenName t) = t

renameCell
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> M.Map (ModeName, GenName) GenName
  -> M.Map (ModeName, Text) Text
  -> Cell2
  -> Either Text Cell2
renameCell modeRen modRen attrRen tyRen permRen genRen cellRen cell = do
  let mode = dMode (c2LHS cell)
  let mode' = renameModeName modeRen mode
  let name' = M.findWithDefault (c2Name cell) (mode', c2Name cell) cellRen
  lhs' <- renameDiagram modeRen modRen attrRen tyRen permRen genRen (c2LHS cell)
  rhs' <- renameDiagram modeRen modRen attrRen tyRen permRen genRen (c2RHS cell)
  pure cell
    { c2Name = name'
    , c2LHS = lhs'
    , c2RHS = rhs'
    }

renameDiagram
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> M.Map (ModeName, GenName) GenName
  -> Diagram
  -> Either Text Diagram
renameDiagram modeRen modRen attrRen tyRen permRen genRen diag =
  traverseDiagram onDiag onPayload pure diag
  where
    mode = dMode diag

    onDiag d = do
      dTmCtx' <- mapM (renameTypeExpr modeRen modRen tyRen permRen) (dTmCtx d)
      dPortTy' <- traverse (renameTypeExpr modeRen modRen tyRen permRen) (dPortTy d)
      pure d
        { dMode = renameModeName modeRen (dMode d)
        , dTmCtx = dTmCtx'
        , dPortTy = dPortTy'
        }

    onPayload payload =
      case payload of
        PGen gen attrs bargs -> do
          let gen' = M.findWithDefault gen (mode, gen) genRen
              attrs' = M.map (renameAttrSortTerm attrRen) attrs
          bargs' <- mapM renameBinderArg bargs
          pure (PGen gen' attrs' bargs')
        PTmMeta v -> do
          sort' <- renameTypeExpr modeRen modRen tyRen permRen (tmvSort v)
          pure (PTmMeta v { tmvSort = sort' })
        _ -> pure payload

    renameBinderArg barg =
      case barg of
        BAConcrete d ->
          BAConcrete <$> renameDiagram modeRen modRen attrRen tyRen permRen genRen d
        BAMeta x -> Right (BAMeta x)

renameAttrSortTerm :: AttrSortRenameMap -> AttrTerm -> AttrTerm
renameAttrSortTerm ren term =
  case term of
    ATLit lit -> ATLit lit
    ATVar v ->
      let sortName' = M.findWithDefault (avSort v) (avSort v) ren
      in ATVar v { avSort = sortName' }

renameInputShape
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> TypeRenameMap
  -> TypePermMap
  -> InputShape
  -> Either Text InputShape
renameInputShape modeRen modRen ren permRen shape =
  case shape of
    InPort ty -> InPort <$> renameTypeExpr modeRen modRen ren permRen ty
    InBinder bs -> InBinder <$> renameBinderSig modeRen modRen ren permRen bs

renameBinderSig
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> TypeRenameMap
  -> TypePermMap
  -> BinderSig
  -> Either Text BinderSig
renameBinderSig modeRen modRen ren permRen sig = do
  tmCtx' <- mapM (renameTypeExpr modeRen modRen ren permRen) (bsTmCtx sig)
  dom' <- mapM (renameTypeExpr modeRen modRen ren permRen) (bsDom sig)
  cod' <- mapM (renameTypeExpr modeRen modRen ren permRen) (bsCod sig)
  pure sig { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }

renameTypeSig
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> TypeRenameMap
  -> TypePermMap
  -> TypeSig
  -> Either Text TypeSig
renameTypeSig modeRen modRen ren permRen sig = do
  params' <- mapM renameParam (tsParams sig)
  pure sig { tsParams = params' }
  where
    renameParam param =
      case param of
        PS_Ty mode -> Right (PS_Ty (renameModeName modeRen mode))
        PS_Tm sortTy -> PS_Tm <$> renameTypeExpr modeRen modRen ren permRen sortTy

renameTypeExpr
  :: M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> TypeRenameMap
  -> TypePermMap
  -> TypeExpr
  -> Either Text TypeExpr
renameTypeExpr modeRen modRen ren permRen ty =
  case ty of
    TVar v ->
      Right (TVar v { tvMode = renameModeName modeRen (tvMode v) })
    TMod me inner -> do
      inner' <- renameTypeExpr modeRen modRen ren permRen inner
      Right (TMod (renameModExpr modeRen modRen me) inner')
    TCon ref args -> do
      args' <- mapM renameArg args
      let ref1 = M.findWithDefault ref ref ren
      let ref' = ref1 { trMode = renameModeName modeRen (trMode ref1) }
      case M.lookup ref permRen of
        Nothing -> Right (TCon ref' args')
        Just perm -> do
          args'' <- applyPerm perm args'
          Right (TCon ref' args'')
  where
    renameArg arg =
      case arg of
        TAType t -> TAType <$> renameTypeExpr modeRen modRen ren permRen t
        TATm tmArg -> TATm <$> renameTermDiagram tmArg

    renameTermDiagram (TermDiagram diag) = do
      let tmCtx' = mapM (renameTypeExpr modeRen modRen ren permRen) (dTmCtx diag)
      let portTy' = mapM (renameTypeExpr modeRen modRen ren permRen) (dPortTy diag)
      tmCtx <- tmCtx'
      portTy <- portTy'
      edges <- mapM renameEdge (dEdges diag)
      Right
        ( TermDiagram
            diag
              { dMode = renameModeName modeRen (dMode diag)
              , dTmCtx = tmCtx
              , dPortTy = portTy
              , dEdges = edges
              }
        )

    renameEdge edge =
      case ePayload edge of
        PTmMeta v -> do
          sort' <- renameTypeExpr modeRen modRen ren permRen (tmvSort v)
          Right edge { ePayload = PTmMeta v { tmvSort = sort' } }
        _ -> Right edge

applyPerm :: [Int] -> [a] -> Either Text [a]
applyPerm perm args
  | length perm /= n = Left "poly pushout: type permutation arity mismatch"
  | any outOfRange perm = Left "poly pushout: type permutation position out of range"
  | length (S.fromList perm) /= n = Left "poly pushout: type permutation is not a bijection"
  | otherwise = Right [ args !! i | i <- perm ]
  where
    n = length args
    outOfRange i = i < 0 || i >= n

mergeDoctrineList :: ModeTheory -> [Doctrine] -> Either Text Doctrine
mergeDoctrineList _ [] = Left "poly pushout: no doctrines to merge"
mergeDoctrineList mt (d:ds) = foldl merge (Right d) ds
  where
    merge acc next = do
      base <- acc
      mergeDoctrine mt base next

mergeDoctrine :: ModeTheory -> Doctrine -> Doctrine -> Either Text Doctrine
mergeDoctrine mt a b = do
  ensureModeTheory "left" a
  ensureModeTheory "right" b
  attrSorts <- mergeAttrSorts (dAttrSorts a) (dAttrSorts b)
  types <- mergeTypeTables (dTypes a) (dTypes b)
  gens <- mergeGenTables (dGens a) (dGens b)
  cells <- mergeCells mt (dCells2 a) (dCells2 b)
  actions <- mergeActions (dActions a) (dActions b)
  obligations <- mergeObligations (dObligations a) (dObligations b)
  let merged =
        a
          { dModes = mt
          , dAcyclicModes = S.union (dAcyclicModes a) (dAcyclicModes b)
          , dAttrSorts = attrSorts
          , dTypes = types
          , dGens = gens
          , dCells2 = cells
          , dActions = actions
          , dObligations = obligations
          }
  validateDoctrine merged
  pure merged
  where
    ensureModeTheory side doc =
      if dModes doc == mt
        then Right ()
        else Left ("poly pushout: " <> side <> " doctrine mode theory mismatch")

    mergeAttrSorts left right =
      foldl add (Right left) (M.toList right)
      where
        add acc (name, decl) = do
          mp <- acc
          case M.lookup name mp of
            Nothing -> Right (M.insert name decl mp)
            Just existing | existing == decl -> Right mp
            _ -> Left "poly pushout: attribute sort conflict"
    mergeTypeTables left right =
      foldl mergeTypeMode (Right left) (M.toList right)
    mergeTypeMode acc (mode, table) = do
      mp <- acc
      let base = M.findWithDefault M.empty mode mp
      merged <- mergeTypeTable base table
      pure (M.insert mode merged mp)
    mergeTypeTable left right =
      foldl add (Right left) (M.toList right)
      where
        add acc (name, sig) = do
          mp <- acc
          case M.lookup name mp of
            Nothing -> Right (M.insert name sig mp)
            Just a | a == sig -> Right mp
            _ -> Left "poly pushout: type signature conflict"
    mergeGenTables left right =
      foldl mergeGenMode (Right left) (M.toList right)
    mergeGenMode acc (mode, table) = do
      mp <- acc
      let base = M.findWithDefault M.empty mode mp
      merged <- mergeGenTable base table
      pure (M.insert mode merged mp)
    mergeGenTable left right =
      foldl add (Right left) (M.elems right)
      where
        add acc gen = do
          mp <- acc
          case M.lookup (gdName gen) mp of
            Nothing -> Right (M.insert (gdName gen) gen mp)
            Just g | genDeclAlphaEq g gen -> Right mp
            _ -> Left "poly pushout: generator conflict"

    mergeActions left right =
      foldl add (Right left) (M.toList right)
      where
        add acc (modName, act) = do
          mp <- acc
          case M.lookup modName mp of
            Nothing -> Right (M.insert modName act mp)
            Just existing
              | existing == act -> Right mp
              | otherwise -> Left "poly pushout: modality action conflict"

    mergeObligations left right =
      foldl add (Right left) right
      where
        add acc obl = do
          obs <- acc
          case filter (\x -> obName x == obName obl) obs of
            [] -> Right (obs <> [obl])
            (existing:_)
              | existing == obl -> Right obs
              | otherwise -> Left "poly pushout: obligation conflict"

mergeCells :: ModeTheory -> [Cell2] -> [Cell2] -> Either Text [Cell2]
mergeCells mt left right =
  foldl insertCell (Right []) (left <> right)
  where
    insertCell acc cell = do
      cells <- acc
      case findNameCollision cell cells of
        Just existing ->
          if bodiesIso cell existing
            then Right (replaceCell existing (mergeCell existing cell) cells)
            else Left ("poly pushout: cell name conflict (" <> c2Name existing <> ", " <> c2Name cell <> ") " <> renderCellDiff existing cell)
        Nothing -> do
          match <- findMatch cell cells
          case match of
            Nothing -> Right (cells <> [cell])
            Just existing ->
              Right (replaceCell existing (mergeCell existing cell) cells)

    findMatch cell cells = do
      matches <- filterM (cellBodyEq cell) cells
      case matches of
        [] -> Right Nothing
        (c:_) -> Right (Just c)

    findNameCollision cell cells =
      case filter (\c -> c2Name c == c2Name cell) cells of
        (c:_) -> Just c
        [] -> Nothing

    bodiesIso a b =
      case cellBodyEq a b of
        Left _ -> False
        Right ok -> ok

    replaceCell target newCell cells =
      let (before, after) = break (\c -> c2Name c == c2Name target) cells
      in case after of
          [] -> cells
          (_:rest) -> before <> [newCell] <> rest

    mergeCell existing incoming =
      let mergedClass =
            if c2Class existing == Structural || c2Class incoming == Structural
              then Structural
              else Computational
          mergedOrient = orientJoin (c2Orient existing) (c2Orient incoming)
      in existing { c2Class = mergedClass, c2Orient = mergedOrient }

    orientJoin a b =
      case (a, b) of
        (Bidirectional, _) -> Bidirectional
        (_, Bidirectional) -> Bidirectional
        (LR, RL) -> Bidirectional
        (RL, LR) -> Bidirectional
        (LR, LR) -> LR
        (RL, RL) -> RL
        (Unoriented, x) -> x
        (x, Unoriented) -> x

    renderCellDiff a b =
      "(" <> renderCellHeader a <> " vs " <> renderCellHeader b <> ")"

    renderCellHeader cell =
      let modeTxt = renderMode (dMode (c2LHS cell))
          domTxt = renderCtx (diagramDom (c2LHS cell))
          codTxt = renderCtx (diagramCod (c2LHS cell))
      in "mode=" <> modeTxt <> ", dom=" <> domTxt <> ", cod=" <> codTxt

    renderCtx res =
      case res of
        Left _ -> "<error>"
        Right ctx -> T.pack (show ctx)

    renderMode (ModeName t) = t

    cellBodyEq a b = do
      if dMode (c2LHS a) /= dMode (c2LHS b)
        then Right False
      else if length (c2TyVars a) /= length (c2TyVars b)
        then Right False
      else if length (c2TmVars a) /= length (c2TmVars b)
        then Right False
        else do
          b' <- alphaRenameCellTo (c2TyVars b) (c2TyVars a) (c2TmVars b) (c2TmVars a) b
          lhsA <- normalizeDiagramModes mt (c2LHS a)
          lhsB <- normalizeDiagramModes mt (c2LHS b')
          rhsA <- normalizeDiagramModes mt (c2RHS a)
          rhsB <- normalizeDiagramModes mt (c2RHS b')
          okL <- isoOrFalse lhsA lhsB
          okR <- isoOrFalse rhsA rhsB
          pure (okL && okR)

    isoOrFalse d1 d2 =
      case diagramIsoEq d1 d2 of
        Left _ -> Right False
        Right ok -> Right ok

genDeclAlphaEq :: GenDecl -> GenDecl -> Bool
genDeclAlphaEq g1 g2 =
  gdMode g1 == gdMode g2
    && gdName g1 == gdName g2
    && gdAttrs g1 == gdAttrs g2
    && length (gdTyVars g1) == length (gdTyVars g2)
    && length (gdTmVars g1) == length (gdTmVars g2)
    && let tyMap = M.fromList (zip (gdTyVars g2) (gdTyVars g1))
           tmMap = M.fromList (zip (gdTmVars g2) (gdTmVars g1))
           tyVars2 = map (renameTyVarAlpha tyMap) (gdTyVars g2)
           tmVars2 = map (renameTmVarAlpha tyMap tmMap) (gdTmVars g2)
           dom2 = map (renameInputShapeAlpha tyMap tmMap) (gdDom g2)
           cod2 = map (renameTypeAlpha tyMap tmMap) (gdCod g2)
       in tyVars2 == gdTyVars g1
            && tmVars2 == gdTmVars g1
            && dom2 == gdDom g1
            && cod2 == gdCod g1

alphaRenameCellTo :: [TyVar] -> [TyVar] -> [TmVar] -> [TmVar] -> Cell2 -> Either Text Cell2
alphaRenameCellTo fromTy toTy fromTm toTm cell
  | length fromTy /= length toTy = Left "poly pushout: alpha rename type arity mismatch"
  | length fromTm /= length toTm = Left "poly pushout: alpha rename term-variable arity mismatch"
  | otherwise =
      let tyMap = M.fromList (zip fromTy toTy)
          tmMap = M.fromList (zip fromTm toTm)
          lhs' = renameDiagramAlpha tyMap tmMap (c2LHS cell)
          rhs' = renameDiagramAlpha tyMap tmMap (c2RHS cell)
      in Right cell { c2TyVars = toTy, c2TmVars = toTm, c2LHS = lhs', c2RHS = rhs' }

renameTyVarAlpha :: M.Map TyVar TyVar -> TyVar -> TyVar
renameTyVarAlpha tyMap v =
  M.findWithDefault v v tyMap

renameTmVarAlpha :: M.Map TyVar TyVar -> M.Map TmVar TmVar -> TmVar -> TmVar
renameTmVarAlpha tyMap tmMap v =
  case M.lookup v tmMap of
    Just v' -> v'
    Nothing -> v { tmvSort = renameTypeAlpha tyMap tmMap (tmvSort v) }

renameTypeAlpha :: M.Map TyVar TyVar -> M.Map TmVar TmVar -> TypeExpr -> TypeExpr
renameTypeAlpha tyMap tmMap = mapTypeExpr renameTy renameTm
  where
    renameTy ty =
      case ty of
        TVar v -> TVar (renameTyVarAlpha tyMap v)
        _ -> ty
    renameTm (TermDiagram diag) =
      TermDiagram $
        runIdentity $
          traverseDiagram onDiag onPayload pure diag
      where
        onDiag d =
          pure d
            { dPortTy = IM.map (renameTypeAlpha tyMap tmMap) (dPortTy d)
            , dTmCtx = map (renameTypeAlpha tyMap tmMap) (dTmCtx d)
            }
        onPayload payload =
          pure $
            case payload of
              PTmMeta v -> PTmMeta (renameTmVarAlpha tyMap tmMap v)
              _ -> payload

renameInputShapeAlpha :: M.Map TyVar TyVar -> M.Map TmVar TmVar -> InputShape -> InputShape
renameInputShapeAlpha tyMap tmMap shape =
  case shape of
    InPort ty -> InPort (renameTypeAlpha tyMap tmMap ty)
    InBinder bs ->
      let tmCtx' = map (renameTypeAlpha tyMap tmMap) (bsTmCtx bs)
          dom' = map (renameTypeAlpha tyMap tmMap) (bsDom bs)
          cod' = map (renameTypeAlpha tyMap tmMap) (bsCod bs)
      in InBinder bs { bsTmCtx = tmCtx', bsDom = dom', bsCod = cod' }

renameDiagramAlpha :: M.Map TyVar TyVar -> M.Map TmVar TmVar -> Diagram -> Diagram
renameDiagramAlpha tyMap tmMap =
  runIdentity . traverseDiagram onDiag pure pure
  where
    onDiag d =
      pure d
        { dTmCtx = map (renameTypeAlpha tyMap tmMap) (dTmCtx d)
        , dPortTy = IM.map (renameTypeAlpha tyMap tmMap) (dPortTy d)
        }

normalizeDiagramModes :: ModeTheory -> Diagram -> Either Text Diagram
normalizeDiagramModes mt diag = do
  tmCtx' <- mapM normalizeTypeModes (dTmCtx diag)
  portTy' <- traverse normalizeTypeModes (dPortTy diag)
  edges' <- traverse normalizeEdgeModes (dEdges diag)
  pure diag { dTmCtx = tmCtx', dPortTy = portTy', dEdges = edges' }
  where
    normalizeEdgeModes edge =
      case ePayload edge of
        PGen g attrs bargs -> do
          bargs' <- mapM normalizeBinderArg bargs
          pure edge { ePayload = PGen g attrs bargs' }
        PBox name inner -> do
          inner' <- normalizeDiagramModes mt inner
          pure edge { ePayload = PBox name inner' }
        PFeedback inner -> do
          inner' <- normalizeDiagramModes mt inner
          pure edge { ePayload = PFeedback inner' }
        PSplice x ->
          pure edge { ePayload = PSplice x }
        PTmMeta v -> do
          sort' <- normalizeTypeModes (tmvSort v)
          pure edge { ePayload = PTmMeta v { tmvSort = sort' } }
        PInternalDrop ->
          pure edge { ePayload = PInternalDrop }

    normalizeBinderArg barg =
      case barg of
        BAConcrete inner -> BAConcrete <$> normalizeDiagramModes mt inner
        BAMeta x -> Right (BAMeta x)

    normalizeTypeModes ty = do
      ty' <- goType ty
      normalizeTypeExpr mt ty'

    goType ty =
      case ty of
        TVar _ -> Right ty
        TCon ref args -> do
          args' <- mapM goArg args
          Right (TCon ref args')
        TMod me inner -> do
          inner' <- goType inner
          Right (TMod me inner')

    goArg arg =
      case arg of
        TAType ty -> TAType <$> goType ty
        TATm tmArg -> TATm <$> goTm tmArg

    goTm (TermDiagram diag) = do
      tmCtx' <- mapM goType (dTmCtx diag)
      portTy' <- mapM goType (dPortTy diag)
      edges' <- mapM goEdge (dEdges diag)
      Right
        ( TermDiagram
            diag
              { dTmCtx = tmCtx'
              , dPortTy = portTy'
              , dEdges = edges'
              }
        )

    goEdge edge =
      case ePayload edge of
        PTmMeta v -> do
          sort' <- goType (tmvSort v)
          Right edge { ePayload = PTmMeta v { tmvSort = sort' } }
        _ -> Right edge

buildInj
  :: Text
  -> Doctrine
  -> Doctrine
  -> M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> M.Map (ModeName, GenName) GenName
  -> Either Text Morphism
buildInj name src tgt modeRen modRen attrRen tyRen permRen genRen = do
  attrSortMap <- buildAttrSortMap src attrRen
  typeMap <- buildTypeMap src modeRen modRen tyRen permRen
  genMap <- buildGenMap src tgt modeRen modRen attrRen tyRen permRen genRen
  pure Morphism
    { morName = name
    , morSrc = src
    , morTgt = tgt
    , morIsCoercion = True
    , morModeMap = buildModeMap src modeRen
    , morModMap = buildModMap src modeRen modRen
    , morAttrSortMap = attrSortMap
    , morTypeMap = typeMap
    , morGenMap = genMap
    , morCheck = CheckAll
    , morPolicy = UseOnlyComputationalLR
    }

buildModeMap :: Doctrine -> M.Map ModeName ModeName -> M.Map ModeName ModeName
buildModeMap src ren =
  M.fromList
    [ (mode, renameModeName ren mode)
    | mode <- M.keys (mtModes (dModes src))
    ]

buildModMap :: Doctrine -> M.Map ModeName ModeName -> M.Map ModName ModName -> M.Map ModName ModExpr
buildModMap src modeRen modRen =
  M.fromList
    [ (name, image decl)
    | (name, decl) <- M.toList (mtDecls (dModes src))
    ]
  where
    image decl =
      ModExpr
        { meSrc = renameModeName modeRen (mdSrc decl)
        , meTgt = renameModeName modeRen (mdTgt decl)
        , mePath = [renameModName modRen (mdName decl)]
        }

buildAttrSortMap :: Doctrine -> AttrSortRenameMap -> Either Text (M.Map AttrSort AttrSort)
buildAttrSortMap doc renames =
  foldM add M.empty (M.keys (dAttrSorts doc))
  where
    add mp srcSort =
      let tgtSort = M.findWithDefault srcSort srcSort renames
      in Right (M.insert srcSort tgtSort mp)

buildTypeMap
  :: Doctrine
  -> M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> TypeRenameMap
  -> TypePermMap
  -> Either Text (M.Map TypeRef TypeTemplate)
buildTypeMap doc modeRen modRen renames permRen = do
  tt <- doctrineTypeTheory doc
  foldM (add tt) M.empty (allTypes doc)
  where
    add tt mp (ref, sig) = do
      let ref0 = M.findWithDefault ref ref renames
      let ref' = ref0 { trMode = renameModeName modeRen (trMode ref0) }
      let mPerm = M.lookup ref permRen
      if ref' == ref && mPerm == Nothing
        then Right mp
        else do
          tmpl <- renameTemplate tt ref' mPerm (tsParams sig)
          Right (M.insert ref tmpl mp)
    renameTemplate tt tgtRef mPerm params = do
      tmplParams <- mapM mkParam (zip [0 :: Int ..] params)
      args0 <- mapM (toArg tt) tmplParams
      args <- case mPerm of
        Nothing -> Right args0
        Just perm -> applyPerm perm args0
      pure (TypeTemplate tmplParams (TCon tgtRef args))

    mkParam (i, param) =
      case param of
        PS_Ty mode ->
          Right (TPType TyVar { tvName = "a" <> T.pack (show i), tvMode = renameModeName modeRen mode })
        PS_Tm sortTy -> do
          sortTy' <- renameTypeExpr modeRen modRen renames permRen sortTy
          Right (TPTm TmVar { tmvName = "i" <> T.pack (show i), tmvSort = sortTy', tmvScope = 0 })

    toArg tt param =
      case param of
        TPType v -> Right (TAType (TVar v))
        TPTm v -> do
          tm <- termExprToDiagramChecked tt [] (tmvSort v) (TMVar v)
          Right (TATm tm)

buildGenMap
  :: Doctrine
  -> Doctrine
  -> M.Map ModeName ModeName
  -> M.Map ModName ModName
  -> AttrSortRenameMap
  -> TypeRenameMap
  -> TypePermMap
  -> M.Map (ModeName, GenName) GenName
  -> Either Text (M.Map (ModeName, GenName) GenImage)
buildGenMap src tgt modeRen modRen attrRen tyRen permRen genRen =
  fmap M.fromList (mapM build (allGens src))
  where
    build (mode, gen) = do
      let genName = gdName gen
      let mode' = renameModeName modeRen mode
      let genName' = M.findWithDefault genName (mode, genName) genRen
      dom <- mapM (renameTypeExpr modeRen modRen tyRen permRen) (gdPlainDom gen)
      cod <- mapM (renameTypeExpr modeRen modRen tyRen permRen) (gdCod gen)
      _ <- ensureGenExists tgt mode' genName'
      let attrs =
            M.fromList
              [ (fieldName, ATVar (AttrVar fieldName (M.findWithDefault sortName sortName attrRen)))
              | (fieldName, sortName) <- gdAttrs gen
              ]
      d0 <- genDWithAttrs mode' dom cod genName' attrs
      let binderSlots = [ bs | InBinder bs <- gdDom gen ]
      binderSlotsRenamed <- mapM (renameBinderSig modeRen modRen tyRen permRen) binderSlots
      let holes = [ BinderMetaVar ("b" <> T.pack (show i)) | i <- [0 .. length binderSlots - 1] ]
      let bargs = map BAMeta holes
      let binderSigs = M.fromList (zip holes binderSlotsRenamed)
      d <- setSingleGenBargs genName' attrs bargs d0
      pure ((mode, genName), GenImage d binderSigs)

    setSingleGenBargs genName attrs bargs diag =
      case IM.toList (dEdges diag) of
        [(edgeKey, edge)] ->
          let edge' = edge { ePayload = PGen genName attrs bargs }
          in Right diag { dEdges = IM.insert edgeKey edge' (dEdges diag) }
        _ -> Left "poly pushout: generated image is not a single generator edge"

checkGenerated :: Text -> Morphism -> Either Text ()
checkGenerated label mor =
  case checkMorphism mor of
    Left err -> Left ("poly pushout generated morphism " <> label <> " invalid: " <> err)
    Right () -> Right ()

allTypes :: Doctrine -> [(TypeRef, TypeSig)]
allTypes doc =
  [ (TypeRef mode name, sig)
  | (mode, table) <- M.toList (dTypes doc)
  , (name, sig) <- M.toList table
  ]

allGens :: Doctrine -> [(ModeName, GenDecl)]
allGens doc =
  [ (mode, gen)
  | (mode, table) <- M.toList (dGens doc)
  , gen <- M.elems table
  ]
