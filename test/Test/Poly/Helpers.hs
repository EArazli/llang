{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.Helpers
  ( mkModes
  , mkModesFromSet
  , selfClassifiedModes
  , withSelfClassifiedCtors
  , withZeroParamGenArgSigs
  , identityModeMap
  , identityModMap
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import Strat.Poly.Doctrine (Doctrine(..))
import Strat.Poly.Doctrine (GenDecl(..), GenParam(..), InputShape(..))
import Strat.Poly.Graph (Diagram)
import Strat.Poly.GenArgSigs (withStructuralZeroParamGenArgSigs)
import Strat.Poly.ModeTheory
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Obj (Obj, ObjName(..), ObjRef(..), TmVar(..), mkCon)
import Strat.Poly.TypeTheory (TypeTheory)
import Test.Poly.CtorSigCompat (TypeParamSig(..), flatParamsToGenParams)


mkModes :: [ModeName] -> ModeTheory
mkModes modes =
  ModeTheory
    { mtModes = M.fromList [ (m, ModeInfo { miName = m, miDefEqEngine = DefEqTRS }) | m <- modes ]
    , mtDecls = M.empty
    , mtEqns = []
    , mtTransforms = M.empty
    , mtClassifiedBy = M.empty
    , mtClassifierLifts = M.empty
    }

mkModesFromSet :: S.Set ModeName -> ModeTheory
mkModesFromSet = mkModes . S.toList

universeName :: ModeName -> ObjName
universeName (ModeName n) = ObjName ("U_" <> n)

universeObj :: ModeName -> Obj
universeObj mode = mkCon (ObjRef mode (universeName mode)) []

compCtxExtName :: GenName
compCtxExtName = GenName "comp_ctx_ext"

compVarName :: GenName
compVarName = GenName "comp_var"

compReindexName :: GenName
compReindexName = GenName "comp_reindex"

compDecl :: CompDecl
compDecl =
  CompDecl
    { compCtxExt = compCtxExtName
    , compVar = compVarName
    , compReindex = compReindexName
    }

selfClassifiedModes :: [ModeName] -> ModeTheory
selfClassifiedModes modes =
  let mt = mkModes modes
   in mt
        { mtClassifiedBy =
            M.fromList
              [ (mode, ClassificationDecl { cdClassifier = mode, cdUniverse = universeObj mode, cdComp = Just compDecl })
              | mode <- modes
              ]
        }

objNameText :: ObjName -> T.Text
objNameText (ObjName n) = n

ctorDecl :: ModeName -> ObjName -> [TypeParamSig] -> GenDecl
ctorDecl mode ctorName sig =
  GenDecl
    { gdName = GenName (objNameText ctorName)
    , gdMode = mode
    , gdParams = flatParamsToGenParams mode sig
    , gdDom = []
    , gdCod = [universeObj mode]
    , gdLiteralKind = Nothing
    }

addSelfClassifications :: [ModeName] -> ModeTheory -> ModeTheory
addSelfClassifications modes mt =
  mt
    { mtClassifiedBy =
        foldl
          (\acc mode ->
              M.insertWith
                (\_ old -> old)
                mode
                (ClassificationDecl { cdClassifier = mode, cdUniverse = universeObj mode, cdComp = Just compDecl })
                acc
          )
          (mtClassifiedBy mt)
          modes
    }

compSupportGen :: ModeName -> GenName -> GenDecl
compSupportGen mode name =
  GenDecl
    { gdName = name
    , gdMode = mode
    , gdParams = []
    , gdDom = [InPort (universeObj mode)]
    , gdCod = [universeObj mode]
    , gdLiteralKind = Nothing
    }

insertCompSupportGens
  :: ModeName
  -> M.Map ModeName (M.Map GenName GenDecl)
  -> M.Map ModeName (M.Map GenName GenDecl)
insertCompSupportGens mode gens0 =
  let support =
        M.fromList
          [ (compCtxExtName, compSupportGen mode compCtxExtName)
          , (compVarName, compSupportGen mode compVarName)
          , (compReindexName, compSupportGen mode compReindexName)
          ]
      modeMap = M.findWithDefault M.empty mode gens0
   in M.insert mode (M.union modeMap support) gens0

insertCtorDecls
  :: ModeName
  -> [(ObjName, [TypeParamSig])]
  -> M.Map ModeName (M.Map GenName GenDecl)
  -> M.Map ModeName (M.Map GenName GenDecl)
insertCtorDecls mode sigs gens0 =
  let ctorMap =
        M.fromList
          [ (gdName gd, gd)
          | (ctorName, params) <- sigs
          , let gd = ctorDecl mode ctorName params
          ]
      modeMap = M.findWithDefault M.empty mode gens0
   in M.insert mode (M.union modeMap ctorMap) gens0

withSelfClassifiedCtors :: [(ModeName, [(ObjName, [TypeParamSig])])] -> Doctrine -> Doctrine
withSelfClassifiedCtors entries doc =
  doc
    { dModes = addSelfClassifications (map fst entries) (dModes doc)
    , dGens =
        foldl
          (\acc (mode, sigs) -> insertCompSupportGens mode (insertCtorDecls mode sigs acc))
          (dGens doc)
          entries
    }

identityModeMap :: Doctrine -> M.Map ModeName ModeName
identityModeMap doc =
  M.fromList [ (m, m) | m <- M.keys (mtModes (dModes doc)) ]

identityModMap :: Doctrine -> M.Map ModName ModExpr
identityModMap doc =
  M.fromList
    [ (name, ModExpr { meSrc = mdSrc decl, meTgt = mdTgt decl, mePath = [name] })
    | (name, decl) <- M.toList (mtDecls (dModes doc))
    ]

withZeroParamGenArgSigs :: [Diagram] -> TypeTheory -> Either Text TypeTheory
withZeroParamGenArgSigs = withStructuralZeroParamGenArgSigs
