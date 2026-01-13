module Strat.Surface.Combinator
  ( CombTerm(..)
  ) where

import Strat.Surface
import Strat.Kernel.Presentation
import Strat.Kernel.Term (mkOp)
import Data.Text (Text)

data CombTerm
  = CVar Text
  | COp Text [CombTerm]
  deriving (Eq, Show)

instance SurfaceLang CombTerm where
  elaborate inst term =
    case term of
      CVar name ->
        case diResolveVar inst name of
          Just t -> Right t
          Nothing -> Left (UnknownVar name)
      COp name args -> do
        opName <- case diResolveOp inst name of
          Just op -> Right op
          Nothing -> Left (UnknownOp name)
        args' <- mapM (elaborate inst) args
        case mkOp (presSig (diPresentation inst)) opName args' of
          Left err -> Left (ElabTypeError err)
          Right t -> Right t
