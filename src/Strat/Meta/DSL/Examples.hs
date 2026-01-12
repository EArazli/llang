{-# LANGUAGE OverloadedStrings #-}
module Strat.Meta.DSL.Examples where

import Data.Text (Text)
import qualified Data.Text as T

exampleDisjointShared :: Text
exampleDisjointShared =
  T.unlines
    [ "doctrine A where { computational r : f(?x) -> g(?x); }"
    , "doctrine B where { computational r : f(?x) -> h(?x); }"
    , "doctrine AB = A & B;"
    , "doctrine ABshared = share syms { A.f = B.f } in (A & B);"
    ]

exampleExtends :: Text
exampleExtends =
  T.unlines
    [ "doctrine Base where { computational base : f(?x) -> ?x; }"
    , "doctrine Ext where { computational ext : k(f(?x)) -> ?x; }"
    , "doctrine C = (Base@C) & (Ext@C);"
    ]

exampleRename :: Text
exampleRename =
  T.unlines
    [ "doctrine A where { computational r : f(?x) -> g(?x); }"
    , "doctrine Arenamed = rename syms { A.g -> A.g2 } in A;"
    ]
