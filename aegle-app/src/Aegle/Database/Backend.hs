module Aegle.Database.Backend
  ( Referent (..),
    LibraryItem (..),
    DefKind (..),
    DbReader (..),
    resolveNames,
    loadCandidates,
    Definition (..),
    Export (..),
    LibraryFragment (..),
    DbBuilder,
  )
where

import Aegle.Core.Name
import Aegle.Core.Term
import Aegle.Prelude
import Aegle.Search.Feature
import Control.Foldl qualified as Foldl
import Data.Text qualified as T

--------------------------------------------------------------------------------
-- Build operation

data Definition = Definition
  { name :: QName,
    kind :: DefKind,
    signature :: Type,
    originalSignature :: Type,
    feature :: AllFeature QName,
    body :: Maybe Term,
    moduleName :: ModuleName,
    position :: Int
  }
  deriving stock (Show, Generic)

data DefKind
  = DKPostulate
  | DKFunction
  | DKDatatype
  | DKRecord
  | DKConstructor
  | DKPrimitive
  deriving stock (Eq, Ord, Show, Enum, Bounded, Generic)
  deriving anyclass (NFData)

data Export = Export
  { canonicalName :: QName,
    exportAs :: QName
  }
  deriving stock (Show, Generic)

data LibraryFragment = LibraryFragment
  { definitions :: [Definition],
    exports :: [Export]
  }
  deriving stock (Show, Generic)
  deriving (Semigroup, Monoid) via Generically LibraryFragment

-- | Build database by consuming library fragments.
-- Note that exports in earlier fragments may refer to canonical names defined in later ones.
type DbBuilder m = Foldl.FoldM m LibraryFragment

--------------------------------------------------------------------------------
-- Read operation

data Referent = Referent
  { canonicalName :: QName,
    body :: Maybe Term
  }
  deriving stock (Show, Generic)

data LibraryItem = LibraryItem
  { canonicalName :: QName,
    kind :: DefKind,
    reexportedAs :: [QName],
    signature :: Type,
    originalSignature :: Type,
    moduleName :: ModuleName,
    position :: Int
  }
  deriving stock (Show, Generic)
  deriving anyclass (NFData)

data DbReader m = DbReader
  { resolveNames ::
      forall t.
      (Traversable t) => t PQName -> m (t [Referent]),
    loadCandidates ::
      [T.Text] ->
      [Compat (FilterFeature PQName)] ->
      m [LibraryItem]
  }

-- | Resolve possibly-qualified names.
resolveNames :: (Traversable t) => DbReader m -> t PQName -> m (t [Referent])
resolveNames DbReader {..} = resolveNames

-- | Load library items
--   * whose names contain all the given texts as substrings
--   * whose type signatures match at least one of the given compatibilities.
--
-- Note that the compatibilities may contain unresolved names.
loadCandidates :: DbReader m -> [T.Text] -> [Compat (FilterFeature PQName)] -> m [LibraryItem]
loadCandidates DbReader {..} = loadCandidates
