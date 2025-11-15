module Pudding.Types.Base where

import GHC.Base (Symbol)
import Prettyprinter (Pretty)
import Control.DeepSeq (NFData)

-- Annotate a data field with a name
infixr 9 @::
type (@::) (s :: Symbol) t = t

-- Fresh integers.
-- E.g. for numbering typed holes
newtype Fresh = Fresh Int
  deriving newtype (Eq, Ord, Show, Pretty, NFData)

-- | When we go into the unification/conversion checking algorithm, we need to
-- ask it how to relate its arguments. A "more general" type subsumes a
-- "more specific" type that a term already had.
--
-- Places where this matters:
--
--   - Universe levels: the subsumption mode determines which constraint to add
--   - Implicit arguments
--   - Uhh there is no structural subtyping, i think ...
data UnifyMode
  = RSubsumesL RequestSubsumption -- e.g. (t : l) : r
  | LSubsumesR RequestSubsumption -- e.g. id {l} (t : r)
  | Invariant RequestSubsumption -- e.g. l = r

-- | Each unification mode can generate a subsumption (an actual term to mediate
-- between different representations), or it can force it to be the identity
-- (which does not imply that no work is done, just not work that is
-- visible to computation: for example, universe levels do not have to be equal,
-- as they are not relevant to computation, they just have to be related by
-- the appropriate constraints).
--
-- Additionally there might need to be a mode for elaboration? Deferred elab?
data RequestSubsumption = GenerateSubsumption | IdentitySubsumption

shouldSubsume :: UnifyMode -> RequestSubsumption
shouldSubsume = \case
  LSubsumesR sub -> sub
  RSubsumesL sub -> sub
  Invariant sub -> sub
