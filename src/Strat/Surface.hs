module Strat.Surface
  ( DoctrineInstance(..)
  , ElabError(..)
  , SurfaceLang(..)
  , defaultInstance
  , withVars
  ) where

import Strat.Kernel.Presentation
import Strat.Kernel.Signature
import Strat.Kernel.Syntax
import Strat.Kernel.Term
import qualified Data.Map.Strict as M
import Data.Text (Text)

data DoctrineInstance = DoctrineInstance
  { diPresentation :: Presentation
  , diResolveOp    :: Text -> Maybe OpName
  , diResolveVar   :: Text -> Maybe Term
  }

data ElabError
  = UnknownOp Text
  | UnknownVar Text
  | ElabTypeError TypeError
  deriving (Eq, Show)

class SurfaceLang ast where
  elaborate :: DoctrineInstance -> ast -> Either ElabError Term

defaultInstance :: Presentation -> DoctrineInstance
defaultInstance pres =
  DoctrineInstance
    { diPresentation = pres
    , diResolveOp = \name ->
        let op = OpName name
        in if M.member op (sigOps (presSig pres)) then Just op else Nothing
    , diResolveVar = \_ -> Nothing
    }

withVars :: M.Map Text Term -> DoctrineInstance -> DoctrineInstance
withVars vars inst =
  inst { diResolveVar = \name -> M.lookup name vars }
