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
import Strat.Poly.TypeExpr


preludeDoctrines :: M.Map Text Doctrine
preludeDoctrines =
  M.fromList
    [ (dName docDoctrine, docDoctrine)
    , (dName fileTreeDoctrine, fileTreeDoctrine)
    ]


docDoctrine :: Doctrine
docDoctrine =
  Doctrine
    { dName = "Doc"
    , dModes = singleMode docMode
    , dAcyclicModes = S.singleton docMode
    , dIndexModes = S.empty
    , dIxTheory = M.empty
    , dAttrSorts =
        M.fromList
          [ (strSort, AttrSortDecl strSort (Just LKString))
          , (intSort, AttrSortDecl intSort (Just LKInt))
          ]
    , dTypes = M.singleton docMode (M.singleton (TypeName "Doc") (TypeSig []))
    , dGens = M.singleton docMode gens
    , dCells2 = []
    }
  where
    gens =
      M.fromList
        [ (GenName "empty", simpleGen "empty" [] [docTy] [])
        , (GenName "text", simpleGen "text" [] [docTy] [("s", strSort)])
        , (GenName "line", simpleGen "line" [] [docTy] [])
        , (GenName "cat", simpleGen "cat" [docTy, docTy] [docTy] [])
        , (GenName "indent", simpleGen "indent" [docTy] [docTy] [("n", intSort)])
        ]
    docTy = TCon (TypeRef docMode (TypeName "Doc")) []


fileTreeDoctrine :: Doctrine
fileTreeDoctrine =
  Doctrine
    { dName = "FileTree"
    , dModes = singleMode fileTreeMode
    , dAcyclicModes = S.singleton fileTreeMode
    , dIndexModes = S.empty
    , dIxTheory = M.empty
    , dAttrSorts =
        M.fromList
          [ (strSort, AttrSortDecl strSort (Just LKString))
          ]
    , dTypes = M.singleton fileTreeMode (M.singleton (TypeName "FileTree") (TypeSig []))
    , dGens = M.singleton fileTreeMode gens
    , dCells2 = []
    }
  where
    gens =
      M.fromList
        [ (GenName "singleFile", simpleGen "singleFile" [] [ftTy] [("path", strSort), ("content", strSort)])
        , (GenName "concatTree", simpleGen "concatTree" [ftTy, ftTy] [ftTy] [])
        ]
    ftTy = TCon (TypeRef fileTreeMode (TypeName "FileTree")) []


docMode :: ModeName
docMode = ModeName "Doc"


fileTreeMode :: ModeName
fileTreeMode = ModeName "FileTree"


strSort :: AttrSort
strSort = AttrSort "Str"


intSort :: AttrSort
intSort = AttrSort "Int"


singleMode :: ModeName -> ModeTheory
singleMode mode =
  case addMode mode emptyModeTheory of
    Left err -> error ("prelude singleMode: " <> show err)
    Right mt -> mt


simpleGen :: Text -> Context -> Context -> [(AttrName, AttrSort)] -> GenDecl
simpleGen name dom cod attrs =
  GenDecl
    { gdName = GenName name
    , gdMode = modeFromCtx cod
    , gdTyVars = []
    , gdIxVars = []
    , gdDom = map InPort dom
    , gdCod = cod
    , gdAttrs = attrs
    }
  where
    modeFromCtx [] =
      case dom of
        (ty:_) -> typeMode ty
        [] -> error "prelude simpleGen: empty domain and codomain"
    modeFromCtx (ty:_) = typeMode ty
