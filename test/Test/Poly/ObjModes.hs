{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Test.Poly.ObjModes
  ( tests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.IntMap.Strict as IM

import Strat.Poly.Obj
  ( Obj(..)
  , mkCon
  , ObjName(..)
  , ObjRef(..)
  , TmVar(..)
  , ObjVar
  , pattern ObjVar
  , ovName
  , ovMode
  , ObjArg
  , pattern OAObj
  , pattern OATm
  , objMode
  )
import Strat.Poly.ModeTheory (ModeName(..), ModeTheory(..), ModeInfo(..), ClassificationDecl(..), emptyModeTheory)
import Strat.Poly.Names (GenName(..))
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), GenParam(..), validateDoctrine)
import Strat.Poly.DSL.Parse (parseDiagExpr)
import Strat.Poly.DSL.Elab (elabDiagExpr)
import Strat.Frontend.Env (emptyEnv)
import Strat.Poly.Diagram (diagramDom)
import Strat.Poly.UnifyObj (unifyObj)
import Strat.Poly.Graph (Diagram(..), emptyDiagram, freshPort, validateDiagram)
import Strat.Poly.TypeTheory (modeOnlyTypeTheory, TypeParamSig(..))


tests :: TestTree
tests =
  testGroup
    "Poly.ObjModes"
    [ testCase "elaboration handles cross-mode nesting" testElabCrossMode
    , testCase "unqualified constructor resolves in expected owner mode" testUnqualifiedConstructorResolvesExpectedMode
    , testCase "wrong qualifier for argument owner mode is rejected" testArgWrongQualifier
    , testCase "unify rejects mode mismatch" testUnifyModeMismatch
    , testCase "validateDiagram rejects port mode mismatch" testValidateDiagramModeMismatch
    , testCase "diagram ports store Obj in the diagram mode" testDiagramPortsStoreObj
    ]

modeC :: ModeName
modeC = ModeName "C"

modeV :: ModeName
modeV = ModeName "V"

tvar :: ModeName -> Text -> ObjVar
tvar mode name = ObjVar { ovName = name, ovMode = mode }

tcon :: ModeName -> Text -> [Obj] -> Obj
tcon mode name args = mkCon (ObjRef mode (ObjName name)) (map OAObj args)

mkDoctrine :: [(ModeName, [(ObjName, [TypeParamSig])])] -> Doctrine
mkDoctrine tables =
  Doctrine
    { dName = "D"
    , dModes = selfClassifiedModes (S.fromList (map fst tables))
    , dAcyclicModes = S.empty
    , dAttrSorts = M.empty
    , dGens =
        foldl
          (\acc (mode, sigs) -> M.insert mode (M.fromList [ (gdName g, g) | g <- map (uncurry (ctorDecl mode)) sigs ]) acc)
          M.empty
          tables
    , dCells2 = []
    , dActions = M.empty
    , dObligations = []
    }

mkModes :: S.Set ModeName -> ModeTheory
mkModes modes =
  ModeTheory
    { mtModes = M.fromList [ (m, ModeInfo m) | m <- S.toList modes ]
    , mtDecls = M.empty
    , mtEqns = []
    , mtTransforms = M.empty
    , mtClassifiedBy = M.empty
    }

selfClassifiedModes :: S.Set ModeName -> ModeTheory
selfClassifiedModes modes =
  let mt = mkModes modes
   in mt
        { mtClassifiedBy =
            M.fromList
              [ ( mode
                , ClassificationDecl
                    { cdClassifier = mode
                    , cdUniverse = mkCon (ObjRef mode (ObjName "U")) []
                    , cdTag = Nothing
                    }
                )
              | mode <- S.toList modes
              ]
        }

objNameText :: ObjName -> Text
objNameText (ObjName n) = n

ctorDecl :: ModeName -> ObjName -> [TypeParamSig] -> GenDecl
ctorDecl mode ctorName sig =
  GenDecl
    { gdName = GenName (objNameText ctorName)
    , gdMode = mode
    , gdTyVars = tyVars
    , gdTmVars = tmVars
    , gdParams = params
    , gdDom = []
    , gdCod = [mkCon (ObjRef mode (ObjName "U")) []]
    , gdAttrs = []
    }
  where
    tyPos =
      [ (pos, v)
      | (pos, TPS_Ty m) <- zip [0 :: Int ..] sig
      , let v =
              TmVar
                { tmvName = "a" <> T.pack (show pos)
                , tmvSort = mkCon (ObjRef m (ObjName "U")) []
                , tmvScope = pos
                , tmvOwnerMode = Just m
                }
      ]
    tmPos =
      [ (pos, v)
      | (pos, TPS_Tm sortTy) <- zip [0 :: Int ..] sig
      , let v =
              TmVar
                { tmvName = "x" <> T.pack (show pos)
                , tmvSort = sortTy
                , tmvScope = negate (pos + 1)
                , tmvOwnerMode = Just mode
                }
      ]
    tyVars = map snd tyPos
    tmVars = map snd tmPos
    params =
      [ case ps of
          TPS_Ty _ -> GP_Ty (lookupByPos pos tyPos)
          TPS_Tm _ -> GP_Tm (lookupByPos pos tmPos)
      | (pos, ps) <- zip [0 :: Int ..] sig
      ]
    lookupByPos pos xs =
      case lookup pos xs of
        Just v -> v
        Nothing -> error "ctorDecl: missing parameter position"

requireDoc :: Doctrine -> IO Doctrine
requireDoc doc =
  case validateDoctrine doc of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure doc

testElabCrossMode :: Assertion
testElabCrossMode = do
  let doc0 =
        mkDoctrine
          [ (modeC, [(ObjName "A", [])])
          , (modeV, [(ObjName "A", []), (ObjName "Thunk", [TPS_Ty modeC])])
          ]
  doc <- requireDoc doc0
  raw <- case parseDiagExpr "id[V.Thunk(C.A)]" of
    Left err -> assertFailure (T.unpack err)
    Right expr -> pure expr
  diag <- case elabDiagExpr emptyEnv doc modeV [] raw of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  dom <- case diagramDom diag of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  dom @?= [tcon modeV "Thunk" [tcon modeC "A" []]]

testUnqualifiedConstructorResolvesExpectedMode :: Assertion
testUnqualifiedConstructorResolvesExpectedMode = do
  let doc0 =
        mkDoctrine
          [ (modeC, [(ObjName "A", [])])
          , (modeV, [(ObjName "A", [])])
          ]
  doc <- requireDoc doc0
  raw <- case parseDiagExpr "id[A]" of
    Left err -> assertFailure (T.unpack err)
    Right expr -> pure expr
  diag <- case elabDiagExpr emptyEnv doc modeC [] raw of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  dom <- case diagramDom diag of
    Left err -> assertFailure (T.unpack err)
    Right d -> pure d
  dom @?= [tcon modeC "A" []]

testArgWrongQualifier :: Assertion
testArgWrongQualifier = do
  let doc0 =
        mkDoctrine
          [ (modeC, [(ObjName "A", [])])
          , (modeV, [(ObjName "A", []), (ObjName "Thunk", [TPS_Ty modeC])])
          ]
  doc <- requireDoc doc0
  raw <- case parseDiagExpr "id[V.Thunk(V.A)]" of
    Left err -> assertFailure (T.unpack err)
    Right expr -> pure expr
  case elabDiagExpr emptyEnv doc modeV [] raw of
    Left err ->
      assertBool "expected wrong qualifier error" ("qualifier V" `T.isInfixOf` err)
    Right _ -> assertFailure "expected wrong qualifier error"

testUnifyModeMismatch :: Assertion
testUnifyModeMismatch = do
  let aVar = tvar modeC "a"
  let aTy = tcon modeC "A" []
  let tt = modeOnlyTypeTheory emptyModeTheory
  case unifyObj tt (OVar aVar) aTy of
    Left err -> assertFailure (T.unpack err)
    Right _ -> pure ()
  case unifyObj tt (OVar aVar) (tcon modeV "B" []) of
    Left err ->
      assertBool "expected mode mismatch" ("mode mismatch" `T.isInfixOf` err)
    Right _ -> assertFailure "expected mode mismatch failure"

testValidateDiagramModeMismatch :: Assertion
testValidateDiagramModeMismatch = do
  let modeM = ModeName "M"
  let badTy = tcon modeC "A" []
  let (_p0, diag) = freshPort badTy (emptyDiagram modeM [])
  case validateDiagram diag of
    Left err ->
      assertBool "expected port mode mismatch" ("wrong mode" `T.isInfixOf` err)
    Right _ -> assertFailure "expected validateDiagram to reject mode mismatch"

testDiagramPortsStoreObj :: Assertion
testDiagramPortsStoreObj = do
  let modeM = ModeName "M"
      objA = tcon modeM "A" []
      (p0, diag0) = freshPort objA (emptyDiagram modeM [])
      diag = diag0 { dIn = [p0], dOut = [p0] }
  case validateDiagram diag of
    Left err -> assertFailure (T.unpack err)
    Right () -> pure ()
  mapM_ (\o -> objMode o @?= dMode diag) (IM.elems (dPortObj diag))
