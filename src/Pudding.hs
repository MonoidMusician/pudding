module Pudding (parseAndBootGlobals, unsafeRunProver) where

import Data.Text (Text)
import GHC.IO (unsafePerformIO)
import Pudding.Core.Parser (declarations, runParser)
import Pudding.Core.Types (Globals, EvalTypeCtx)
import Pudding.Core.Unify (bootGlobals)
import Pudding.Types.Config (dflt)
import Pudding.Types.Monads (withCtx)
import Pudding.Types.Monads.Prover (Prover, runProverMonad)


parseAndBootGlobals :: Text -> Globals
parseAndBootGlobals source = unsafePerformIO do
  parsed <- runParser declarations "<globals>" source
  case parsed of
    Left err -> error $ show err
    Right booted -> runProverMonad dflt $ bootGlobals booted

unsafeRunProver :: EvalTypeCtx -> Prover t -> t
unsafeRunProver ctx = unsafePerformIO . runProverMonad dflt . withCtx ctx
