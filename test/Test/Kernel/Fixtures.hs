{-# LANGUAGE OverloadedStrings #-}
module Test.Kernel.Fixtures
  ( objName
  , homName
  , objSort
  , homSort
  , opA
  , opB
  , opC
  , opF
  , opG
  , opH
  , opK
  , opM
  , opId
  , sigBasic
  , mkTerm
  , varObj
  ) where

import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import qualified Data.Map.Strict as M
import Data.Text (Text)

objName :: SortName
objName = SortName "Obj"

homName :: SortName
homName = SortName "Hom"

objSort :: Sort
objSort = Sort objName []

homSort :: Term -> Term -> Sort
homSort a b = Sort homName [a, b]

opA, opB, opC, opF, opG, opH, opK, opM, opId :: OpName
opA = OpName "a"
opB = OpName "b"
opC = OpName "c"
opF = OpName "f"
opG = OpName "g"
opH = OpName "h"
opK = OpName "k"
opM = OpName "m"
opId = OpName "id"

sigBasic :: Signature
sigBasic =
  Signature
    { sigSortCtors =
        M.fromList
          [ (objName, SortCtor objName [])
          , (homName, SortCtor homName [objSort, objSort])
          ]
    , sigOps =
        M.fromList
          [ (opA, OpDecl opA [] objSort)
          , (opB, OpDecl opB [] objSort)
          , (opC, OpDecl opC [] objSort)
          , (opF, unaryDecl "op:f" opF)
          , (opG, unaryDecl "op:g" opG)
          , (opH, unaryDecl "op:h" opH)
          , (opK, unaryDecl "op:k" opK)
          , (opM, binaryDecl "op:m" opM)
          , (opId, idDecl)
          ]
    }
  where
    unaryDecl scope name =
      let v = Var (ScopeId scope) 0
      in OpDecl name [Binder v objSort] objSort

    binaryDecl scope name =
      let v0 = Var (ScopeId scope) 0
          v1 = Var (ScopeId scope) 1
      in OpDecl name [Binder v0 objSort, Binder v1 objSort] objSort

    idDecl =
      let v = Var (ScopeId "op:id") 0
          vx = mkVar objSort v
      in OpDecl opId [Binder v objSort] (homSort vx vx)

mkTerm :: Signature -> Text -> [Term] -> Term
mkTerm sig name args =
  case mkOp sig (OpName name) args of
    Left err -> error (show err)
    Right t -> t

varObj :: Text -> Int -> Term
varObj scope ix = mkVar objSort (Var (ScopeId scope) ix)
