{-# LANGUAGE OverloadedStrings #-}
module Test.Poly.FoldSSA
  ( foldSSATests
  ) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified Data.Text as T
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Strat.Backend (Value(..))
import Strat.Model.Spec (DefaultBehavior(..), ModelBackend(..), ModelSpec(..))
import Strat.Poly.Diagram (genD)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), TypeSig(..))
import Strat.Poly.Eval (evalDiagram)
import Strat.Poly.Graph (dIn, dOut, setPortLabel)
import Strat.Poly.ModeTheory (ModeInfo(..), ModeName(..), ModeTheory(..), VarDiscipline(..))
import Strat.Poly.Names (GenName(..))
import Strat.Poly.TypeExpr (TypeExpr(..), TypeName(..), TypeRef(..))


foldSSATests :: TestTree
foldSSATests =
  testGroup
    "Poly.FoldSSA"
    [ testCase "fold_ssa uses labels for open-diagram names" testFoldSSAUsesLabels
    , testCase "fold_ssa emits statements for codomain-0 generators" testFoldSSAStmtEmission
    ]

tcon :: ModeName -> T.Text -> [TypeExpr] -> TypeExpr
tcon mode name args = TCon (TypeRef mode (TypeName name)) args

mkModes :: S.Set ModeName -> ModeTheory
mkModes modes =
  ModeTheory
    (M.fromList [ (m, ModeInfo m Linear) | m <- S.toList modes ])
    M.empty
    []
    []

testFoldSSAUsesLabels :: Assertion
testFoldSSAUsesLabels = do
  let mode = ModeName "M"
  let a = tcon mode "A" []
  diag0 <- case genD mode [a] [a] (GenName "g") of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  inPort <- case dIn diag0 of
    [p] -> pure p
    _ -> assertFailure "expected one input" >> fail "unreachable"
  outPort <- case dOut diag0 of
    [p] -> pure p
    _ -> assertFailure "expected one output" >> fail "unreachable"
  diag1 <- case setPortLabel inPort "x" diag0 of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  diag2 <- case setPortLabel outPort "y" diag1 of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  let gDecl =
        GenDecl
          { gdName = GenName "g"
          , gdMode = mode
          , gdTyVars = []
          , gdDom = [a]
          , gdCod = [a]
          , gdAttrs = []
          }
  let doc =
        Doctrine
          { dName = "D"
          , dModes = mkModes (S.singleton mode)
          , dTypes = M.fromList [(mode, M.fromList [(TypeName "A", TypeSig [])])]
          , dGens = M.fromList [(mode, M.fromList [(GenName "g", gDecl)])]
          , dCells2 = []
          , dAttrSorts = M.empty
          }
  let model = ModelSpec "Fold" [] DefaultSymbolic BackendFoldSSA
  vals <- case evalDiagram doc model diag2 [] of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right xs -> pure xs
  vals @?=
    [ VString
        ( T.intercalate
            "\n"
            [ "(x) => {"
            , "  const y = g(x);"
            , "  return y;"
            , "}"
            ]
        )
    ]

testFoldSSAStmtEmission :: Assertion
testFoldSSAStmtEmission = do
  let mode = ModeName "M"
  diag <- case genD mode [] [] (GenName "emit") of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right d -> pure d
  let doc =
        Doctrine
          { dName = "D"
          , dModes = mkModes (S.singleton mode)
          , dTypes = M.empty
          , dGens =
              M.fromList
                [ ( mode
                  , M.fromList
                      [ ( GenName "emit"
                        , GenDecl
                            { gdName = GenName "emit"
                            , gdMode = mode
                            , gdTyVars = []
                            , gdDom = []
                            , gdCod = []
                            , gdAttrs = []
                            }
                        )
                      ]
                  )
                ]
          , dCells2 = []
          , dAttrSorts = M.empty
          }
  let model = ModelSpec "Fold" [] DefaultSymbolic BackendFoldSSA
  vals <- case evalDiagram doc model diag [] of
    Left err -> assertFailure (T.unpack err) >> fail "unreachable"
    Right xs -> pure xs
  vals @?=
    [ VString
        ( T.intercalate
            "\n"
            [ "(() => {"
            , "  emit();"
            , "})()"
            ]
        )
    ]
