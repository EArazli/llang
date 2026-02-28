{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Prelude
  ( preludeDoctrines
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Attr
import Strat.Poly.Doctrine
import Strat.Poly.ModeTheory
import Strat.Poly.Names
import Strat.Poly.Obj


preludeDoctrines :: M.Map Text Doctrine
preludeDoctrines =
  M.fromList
    [ (dName docDoctrine, docDoctrine)
    , (dName artifactDoctrine, artifactDoctrine)
    ]


docDoctrine :: Doctrine
docDoctrine =
  Doctrine
    { dName = "Doc"
    , dModes = singleSelfClassifiedMode docMode
    , dAcyclicModes = S.singleton docMode
    , dAttrSorts =
        M.fromList
          [ (strSort, AttrSortDecl strSort (Just LKString))
          , (intSort, AttrSortDecl intSort (Just LKInt))
          ]
    , dGens = M.singleton docMode gens
    , dCells2 = []
    , dActions = M.empty
    , dObligations = []
    }
  where
    gens =
      M.fromList
        [ (GenName "Doc", ctorGen docMode "Doc")
        , (compCtxExtName, compGen docMode compCtxExtName)
        , (compVarName, compGen docMode compVarName)
        , (compReindexName, compGen docMode compReindexName)
        , (GenName "empty", simpleGen "empty" [] [docTy] [])
        , (GenName "text", simpleGen "text" [] [docTy] [("s", strSort)])
        , (GenName "line", simpleGen "line" [] [docTy] [])
        , (GenName "cat", simpleGen "cat" [docTy, docTy] [docTy] [])
        , (GenName "indent", simpleGen "indent" [docTy] [docTy] [("n", intSort)])
        ]
    docTy = mkCon (ObjRef docMode (ObjName "Doc")) []


artifactDoctrine :: Doctrine
artifactDoctrine =
  Doctrine
    { dName = "Artifact"
    , dModes = singleSelfClassifiedMode artifactMode
    , dAcyclicModes = S.singleton artifactMode
    , dAttrSorts =
        M.fromList
          [ (strSort, AttrSortDecl strSort (Just LKString))
          , (intSort, AttrSortDecl intSort (Just LKInt))
          ]
    , dGens = M.singleton artifactMode gens
    , dCells2 = []
    , dActions = M.empty
    , dObligations = []
    }
  where
    docTy = mkCon (ObjRef artifactMode (ObjName "Doc")) []
    ftTy = mkCon (ObjRef artifactMode (ObjName "FileTree")) []
    gens =
      M.fromList
        [ (GenName "Doc", ctorGen artifactMode "Doc")
        , (GenName "FileTree", ctorGen artifactMode "FileTree")
        , (compCtxExtName, compGen artifactMode compCtxExtName)
        , (compVarName, compGen artifactMode compVarName)
        , (compReindexName, compGen artifactMode compReindexName)
        , (GenName "empty", simpleGen "empty" [] [docTy] [])
        , (GenName "text", simpleGen "text" [] [docTy] [("s", strSort)])
        , (GenName "line", simpleGen "line" [] [docTy] [])
        , (GenName "cat", simpleGen "cat" [docTy, docTy] [docTy] [])
        , (GenName "indent", simpleGen "indent" [docTy] [docTy] [("n", intSort)])
        , (GenName "singleFile", simpleGen "singleFile" [docTy] [ftTy] [("path", strSort)])
        , (GenName "concatTree", simpleGen "concatTree" [ftTy, ftTy] [ftTy] [])
        ]


docMode :: ModeName
docMode = ModeName "Doc"


artifactMode :: ModeName
artifactMode = ModeName "Artifact"


strSort :: AttrSort
strSort = AttrSort "Str"


intSort :: AttrSort
intSort = AttrSort "Int"

compCtxExtName :: GenName
compCtxExtName = GenName "comp_ctx_ext"

compVarName :: GenName
compVarName = GenName "comp_var"

compReindexName :: GenName
compReindexName = GenName "comp_reindex"

preludeCompDecl :: CompDecl
preludeCompDecl =
  CompDecl
    { compCtxExt = compCtxExtName
    , compVar = compVarName
    , compReindex = compReindexName
    }


selfClassifiedMode :: ModeName -> Either Text ModeTheory
selfClassifiedMode mode = do
  mt0 <- addMode mode emptyModeTheory
  addClassification
    mode
    ClassificationDecl
      { cdClassifier = mode
      , cdUniverse = universeObj mode
      
      , cdComp = Just preludeCompDecl
      }
    mt0

singleSelfClassifiedMode :: ModeName -> ModeTheory
singleSelfClassifiedMode mode =
  case selfClassifiedMode mode of
    Left err -> error ("prelude singleSelfClassifiedMode: " <> show err)
    Right mt -> mt

universeName :: ModeName -> ObjName
universeName (ModeName n) = ObjName ("U_" <> n)

universeObj :: ModeName -> Obj
universeObj mode = mkCon (ObjRef mode (universeName mode)) []

ctorGen :: ModeName -> Text -> GenDecl
ctorGen mode name =
  GenDecl
    { gdName = GenName name
    , gdMode = mode
    , gdParams = []
    , gdDom = []
    , gdCod = [universeObj mode]
    , gdAttrs = []
    }

simpleGen :: Text -> Context -> Context -> [(AttrName, AttrSort)] -> GenDecl
simpleGen name dom cod attrs =
  GenDecl
    { gdName = GenName name
    , gdMode = modeFromCtx cod
    , gdParams = []
    , gdDom = map InPort dom
    , gdCod = cod
    , gdAttrs = attrs
    }
  where
    modeFromCtx [] =
      case dom of
        (ty:_) -> objMode ty
        [] -> error "prelude simpleGen: empty domain and codomain"
    modeFromCtx (ty:_) = objMode ty

compGen :: ModeName -> GenName -> GenDecl
compGen mode name =
  GenDecl
    { gdName = name
    , gdMode = mode
    , gdParams = [GP_Ty aVar]
    , gdDom = [InPort aTy]
    , gdCod = [aTy]
    , gdAttrs = []
    }
  where
    aVar =
      TmVar
        { tmvName = "a"
        , tmvSort = universeObj mode
        , tmvScope = 0
        , tmvOwnerMode = Just mode
        }
    aTy = OVar aVar
