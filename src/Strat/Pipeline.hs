{-# LANGUAGE OverloadedStrings #-}
module Strat.Pipeline
  ( FragmentDecl(..)
  , QuoteTargetLayout(..)
  , TransformTypeParam(..)
  , TransformObjectDecl(..)
  , TransformUtility(..)
  , TransformLoopItem(..)
  , TransformerItem(..)
  , TransformerDecl(..)
  , ValueExtractorSpec(..)
  , Phase(..)
  , Pipeline(..)
  , Run(..)
  , DerivedDoctrine(..)
  ) where

import Data.Text (Text)
import qualified Data.Set as S
import Strat.Common.Rules (RewritePolicy)
import Strat.Poly.Names (GenName)


data FragmentDecl = FragmentDecl
  { frName :: Text
  , frBase :: Text
  , frMode :: Text
  , frIncludedGens :: S.Set GenName
  , frCrossBinders :: Bool
  , frCrossBoxes :: Bool
  , frCrossFeedback :: Bool
  }
  deriving (Eq, Show)

data QuoteTargetLayout = QuoteTargetLayout
  { qtlCtxNilCtor :: Text
  , qtlCtxConsCtor :: Text
  , qtlRefCtor :: Text
  , qtlRefsCtor :: Text
  , qtlProgCtor :: Text
  , qtlInputRefsGen :: Text
  , qtlRefsNilGen :: Text
  , qtlRefsConsGen :: Text
  , qtlRefsHeadGen :: Text
  , qtlRefsTailGen :: Text
  , qtlDupRefsGen :: Text
  , qtlDropRefsGen :: Text
  , qtlReturnRefsGen :: Text
  , qtlResidualBoxGen :: Text
  , qtlResidualFeedbackGen :: Text
  , qtlBindingPrefix :: Text
  , qtlResidualPrefix :: Text
  }
  deriving (Eq, Ord, Show)

data TransformTypeParam = TransformTypeParam
  { ttpName :: Text
  , ttpModeVar :: Text
  }
  deriving (Eq, Ord, Show)

data TransformObjectDecl = TransformObjectDecl
  { todName :: Text
  , todParams :: [TransformTypeParam]
  }
  deriving (Eq, Ord, Show)

data TransformUtility
  = TUInputRefs
  | TURefsNil
  | TURefsCons
  | TURefsHead
  | TURefsTail
  | TUDupRefs
  | TUDropRefs
  | TUReturnRefs
  | TUResidualBox
  | TUResidualFeedback
  deriving (Eq, Ord, Show)

data TransformLoopItem
  = TLEmitBindingPrefix Text
  | TLEmitResidualPrefix Text
  deriving (Eq, Ord, Show)

data TransformerItem
  = TICopyDoctrine Text
  | TIEmitObject TransformObjectDecl
  | TIEmitUtility TransformUtility
  | TIForIncludedGenerators
      { tigGenVar :: Text
      , tigFragmentVar :: Text
      , tigItems :: [TransformLoopItem]
      }
  | TIForExcludedGenerators
      { tegGenVar :: Text
      , tegDoctrineVar :: Text
      , tegModeVar :: Text
      , tegFragmentVar :: Text
      , tegItems :: [TransformLoopItem]
      }
  deriving (Eq, Ord, Show)

data TransformerDecl = TransformerDecl
  { tdName :: Text
  , tdSourceDoctrineVar :: Text
  , tdSourceModeVar :: Text
  , tdSourceFragmentVar :: Text
  , tdItems :: [TransformerItem]
  }
  deriving (Eq, Ord, Show)


data ValueExtractorSpec
  = ExtractDoc { veStdout :: Bool }
  | ExtractFileTree { veRoot :: FilePath }
  deriving (Eq, Show)


data Phase
  = ApplyMorph Text
  | Normalize RewritePolicy Int
  | QuoteInto { target :: Text }
  | ExtractValue { doctrine :: Text, extractor :: ValueExtractorSpec }
  | ExtractDiagramPretty
  deriving (Eq, Show)


data Pipeline = Pipeline
  { plName :: Text
  , plPhases :: [Phase]
  }
  deriving (Eq, Show)


data Run = Run
  { runName :: Text
  , runUses :: [Text]
  , runPipeline :: Text
  , runDoctrine :: Text
  , runMode :: Maybe Text
  , runSurface :: Maybe Text
  , runExprText :: Text
  }
  deriving (Eq, Show)


data DerivedDoctrine
  = DerivedTransform
      { ddName :: Text
      , ddBase :: Text
      , ddMode :: Text
      , ddFragment :: Text
      , ddTransformer :: Text
      , ddQuoteLayout :: Maybe QuoteTargetLayout
      }
  deriving (Eq, Show)
