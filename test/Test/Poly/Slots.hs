{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
module Test.Poly.Slots
  ( tests
  ) where

import qualified Data.Map.Strict as M
import qualified Data.Text as T
import Strat.DSL.Elab (elabRawFile)
import Strat.DSL.Parse (parseRawFile)
import Strat.Frontend.Env (meDoctrines)
import Strat.Poly.Doctrine (Doctrine(..), GenDecl(..), deriveCtorTables)
import Strat.Poly.ModeTheory (ModeName(..))
import Strat.Poly.Names (GenName(..), BoxName(..))
import Strat.Poly.Obj
  ( ObjName(..)
  , ObjRef(..)
  , TermDiagram(..)
  , mkCon
  , pattern OATm
  )
import Strat.Poly.Graph (Diagram(..), freshPort, addEdgePayload, validateDiagram, EdgePayload(..))
import Strat.Poly.Diagram (genD, idD)
import Strat.Poly.Slots
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit


tests :: TestTree
tests =
  testGroup
    "Poly.Slots"
    [ testCase "extract slots from ctor term arguments in generator boundaries" testExtractCtorTmSlots
    , testCase "extract slots from binder signatures and nested term arguments" testExtractBinderSlots
    , testCase "extract slots from nested box diagrams inside term arguments" testExtractNestedTermDiagramSlots
    ]

testExtractCtorTmSlots :: Assertion
testExtractCtorTmSlots = do
  doc <- requireDoctrine "SlotCtorTm"
    [ "doctrine SlotCtorTm where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen Nat : [] -> [M.U_M] @M;"
    , "  gen Z : [] -> [Nat] @M;"
    , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
    , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen var(a@M) : [a] -> [a] @M;"
    , "  gen reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
    , "  rule computational ctx_ext_id -> (a@M) : [a] -> [a] @M ="
    , "    ctx_ext{a} == id[a]"
    , "  rule computational var_id -> (a@M) : [a] -> [a] @M ="
    , "    var{a} == id[a]"
    , "  rule computational reindex_id -> (a@M) : [a] -> [a] @M ="
    , "    reindex{a} == id[a]"
    , "  gen use(n : Nat) : [] -> [Vec(n)] @M;"
    , "}"
    ]
  slotsByGen <- requireEither (extractDoctrineSlots doc)
  slots <-
    case M.lookup (ModeName "M", GenName "use") slotsByGen of
      Nothing -> assertFailure "missing slot entry for generator use" >> fail "unreachable"
      Just s -> pure s
  let tmSlots = [ s | s <- slots, slotKind s == SlotCtorTmArg ]
  length tmSlots @?= 1
  case tmSlots of
    [s] -> sidPath (slotId s) @?= "cod[0].arg[0]"
    _ -> assertFailure "expected exactly one term-argument slot in use codomain"

testExtractBinderSlots :: Assertion
testExtractBinderSlots = do
  doc <- requireDoctrine "SlotBinder"
    [ "doctrine SlotBinder where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen Nat : [] -> [M.U_M] @M;"
    , "  gen Z : [] -> [Nat] @M;"
    , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
    , "  gen Out : [] -> [M.U_M] @M;"
    , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen var(a@M) : [a] -> [a] @M;"
    , "  gen reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
    , "  rule computational ctx_ext_id -> (a@M) : [a] -> [a] @M ="
    , "    ctx_ext{a} == id[a]"
    , "  rule computational var_id -> (a@M) : [a] -> [a] @M ="
    , "    var{a} == id[a]"
    , "  rule computational reindex_id -> (a@M) : [a] -> [a] @M ="
    , "    reindex{a} == id[a]"
    , "  gen wrap : [binder { tm n : Nat } : [Vec(Z)]] -> [Out] @M;"
    , "}"
    ]
  slotsByGen <- requireEither (extractDoctrineSlots doc)
  slots <-
    case M.lookup (ModeName "M", GenName "wrap") slotsByGen of
      Nothing -> assertFailure "missing slot entry for generator wrap" >> fail "unreachable"
      Just s -> pure s
  let binderSlots = [ s | s <- slots, slotKind s == SlotBinder ]
  let tmSlots = [ s | s <- slots, slotKind s == SlotCtorTmArg ]
  length binderSlots @?= 1
  assertBool
    "expected nested term slot from binder signature"
    (any (\s -> "dom[0]." `T.isPrefixOf` sidPath (slotId s)) tmSlots)

testExtractNestedTermDiagramSlots :: Assertion
testExtractNestedTermDiagramSlots = do
  doc <- requireDoctrine "SlotNestedTerm"
    [ "doctrine SlotNestedTerm where {"
    , "  mode M classifiedBy M via M.U_M;"
    , "  gen U_M : [] -> [M.U_M] @M;"
    , "  gen Nat : [] -> [M.U_M] @M;"
    , "  gen Z : [] -> [Nat] @M;"
    , "  gen Vec(n : Nat) : [] -> [M.U_M] @M;"
    , "  gen Holder(n : Nat) : [] -> [M.U_M] @M;"
    , "  gen ctx_ext(a@M) : [a] -> [a] @M;"
    , "  gen var(a@M) : [a] -> [a] @M;"
    , "  gen reindex(a@M) : [a] -> [a] @M;"
    , "  comprehension M where { ctx_ext = ctx_ext; var = var; reindex = reindex; };"
    , "  rule computational ctx_ext_id -> (a@M) : [a] -> [a] @M ="
    , "    ctx_ext{a} == id[a]"
    , "  rule computational var_id -> (a@M) : [a] -> [a] @M ="
    , "    var{a} == id[a]"
    , "  rule computational reindex_id -> (a@M) : [a] -> [a] @M ="
    , "    reindex{a} == id[a]"
    , "  gen mk : [] -> [Holder(Z)] @M;"
    , "}"
    ]
  ctorTables <- requireEither (deriveCtorTables doc)
  mkGen <- lookupGen doc (ModeName "M") (GenName "mk")
  mode <- pure (ModeName "M")
  let nat = mkCon (ObjRef mode (ObjName "Nat")) []
  zDiag <- requireEither (genD mode [] [nat] (GenName "Z"))
  let zTerm = TermDiagram zDiag
  let vecZ = mkCon (ObjRef mode (ObjName "Vec")) [OATm zTerm]
  let inner = idD mode [vecZ]
  let (pin, d1) = freshPort vecZ zDiag
  let (pout, d2) = freshPort vecZ d1
  d3 <- requireEither (addEdgePayload (PBox (BoxName "nested") inner) [pin] [pout] d2)
  let d4 = d3 { dIn = dIn d3 <> [pin], dOut = dOut d3 <> [pout] }
  _ <- requireEither (validateDiagram d4)
  let nestedTerm = TermDiagram d4
  let holderTy = mkCon (ObjRef mode (ObjName "Holder")) [OATm nestedTerm]
  let mkGen' = mkGen { gdCod = [holderTy] }
  slots <- requireEither (extractGenSlotsWithTables doc ctorTables mkGen')
  let tmSlots = [ s | s <- slots, slotKind s == SlotCtorTmArg ]
  assertBool "expected base term-argument slot" (any (\s -> sidPath (slotId s) == "cod[0].arg[0]") tmSlots)
  assertBool
    "expected nested slots from term diagram box payload"
    (any (\s -> ".box." `T.isInfixOf` sidPath (slotId s)) tmSlots)

lookupGen :: Doctrine -> ModeName -> GenName -> IO GenDecl
lookupGen doc mode name =
  case M.lookup mode (dGens doc) >>= M.lookup name of
    Nothing ->
      assertFailure ("missing generator " <> show name <> " in mode " <> show mode) >> fail "unreachable"
    Just gd -> pure gd

requireDoctrine :: T.Text -> [T.Text] -> IO Doctrine
requireDoctrine doctrineName lines0 = do
  env <- requireEither (parseRawFile (T.unlines lines0) >>= elabRawFile)
  case M.lookup doctrineName (meDoctrines env) of
    Nothing -> assertFailure ("missing doctrine: " <> T.unpack doctrineName) >> fail "unreachable"
    Just doc -> pure doc

requireEither :: Either T.Text a -> IO a
requireEither =
  either (assertFailure . T.unpack) pure
