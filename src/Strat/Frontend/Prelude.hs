{-# LANGUAGE OverloadedStrings #-}
module Strat.Frontend.Prelude
  ( preludeDoctrines
  ) where

import Data.Text (Text)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Poly.Doctrine
import Strat.Poly.Literal (LiteralKind(..))
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
    , dGens = M.singleton docMode gens
    , dCells2 = []
    , dBuiltins = []
    , dActions = M.empty
    , dObligations = []
    }
  where
    gens =
      M.fromList
        [ (GenName "Doc", ctorGen docMode "Doc" Nothing)
        , (GenName "Str", ctorGen docMode "Str" (Just LKString))
        , (GenName "Int", ctorGen docMode "Int" (Just LKInt))
        , (compCtxExtName, compGen docMode compCtxExtName)
        , (compVarName, compGen docMode compVarName)
        , (compReindexName, compGen docMode compReindexName)
        , (GenName "empty", simpleGen "empty" [] [docTy] [])
        , (GenName "text", simpleGen "text" [] [docTy] [termParam docMode "s" strTy])
        , (GenName "line", simpleGen "line" [] [docTy] [])
        , (GenName "cat", simpleGen "cat" [docTy, docTy] [docTy] [])
        , (GenName "indent", simpleGen "indent" [docTy] [docTy] [termParam docMode "n" intTy])
        ]
    docTy = preludeTy docMode "Doc"
    strTy = preludeTy docMode "Str"
    intTy = preludeTy docMode "Int"


artifactDoctrine :: Doctrine
artifactDoctrine =
  Doctrine
    { dName = "Artifact"
    , dModes = singleSelfClassifiedMode artifactMode
    , dAcyclicModes = S.singleton artifactMode
    , dGens = M.singleton artifactMode gens
    , dCells2 = []
    , dBuiltins = []
    , dActions = M.empty
    , dObligations = []
    }
  where
    docTy = preludeTy artifactMode "Doc"
    ftTy = preludeTy artifactMode "FileTree"
    strTy = preludeTy artifactMode "Str"
    intTy = preludeTy artifactMode "Int"
    gens =
      M.fromList
        [ (GenName "Doc", ctorGen artifactMode "Doc" Nothing)
        , (GenName "FileTree", ctorGen artifactMode "FileTree" Nothing)
        , (GenName "Str", ctorGen artifactMode "Str" (Just LKString))
        , (GenName "Int", ctorGen artifactMode "Int" (Just LKInt))
        , (compCtxExtName, compGen artifactMode compCtxExtName)
        , (compVarName, compGen artifactMode compVarName)
        , (compReindexName, compGen artifactMode compReindexName)
        , (GenName "empty", simpleGen "empty" [] [docTy] [])
        , (GenName "text", simpleGen "text" [] [docTy] [termParam artifactMode "s" strTy])
        , (GenName "line", simpleGen "line" [] [docTy] [])
        , (GenName "cat", simpleGen "cat" [docTy, docTy] [docTy] [])
        , (GenName "indent", simpleGen "indent" [docTy] [docTy] [termParam artifactMode "n" intTy])
        , (GenName "singleFile", simpleGen "singleFile" [docTy] [ftTy] [termParam artifactMode "path" strTy])
        , (GenName "concatTree", simpleGen "concatTree" [ftTy, ftTy] [ftTy] [])
        ]


docMode :: ModeName
docMode = ModeName "Doc"


artifactMode :: ModeName
artifactMode = ModeName "Artifact"


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

preludeTy :: ModeName -> Text -> Obj
preludeTy mode name = mkCon (ObjRef mode (ObjName name)) []

ctorGen :: ModeName -> Text -> Maybe LiteralKind -> GenDecl
ctorGen mode name litKind =
  GenDecl
    { gdName = GenName name
    , gdMode = mode
    , gdParams = []
    , gdDom = []
    , gdCod = [universeObj mode]
    , gdLiteralKind = litKind
    }

simpleGen :: Text -> Context -> Context -> [GenParam] -> GenDecl
simpleGen name dom cod params =
  GenDecl
    { gdName = GenName name
    , gdMode = modeFromCtx cod
    , gdParams = params
    , gdDom = map InPort dom
    , gdCod = cod
    , gdLiteralKind = Nothing
    }
  where
    modeFromCtx [] =
      case dom of
        (ty:_) -> objMode ty
        [] -> error "prelude simpleGen: empty domain and codomain"
    modeFromCtx (ty:_) = objMode ty

termParam :: ModeName -> Text -> Obj -> GenParam
termParam mode name sortTy =
  GP_Tm
    TmVar
      { tmvName = name
      , tmvSort = sortTy
      , tmvScope = 0
      , tmvOwnerMode = Just mode
      }

compGen :: ModeName -> GenName -> GenDecl
compGen mode name =
  GenDecl
    { gdName = name
    , gdMode = mode
    , gdParams = [GP_Ty aVar]
    , gdDom = [InPort aTy]
    , gdCod = [aTy]
    , gdLiteralKind = Nothing
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
