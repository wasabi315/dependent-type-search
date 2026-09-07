module Aegle.Core.Name
  ( Index (..),
    Level (..),
    Name (..),
    ModuleName (..),
    LibName (..),
    QName (..),
    PQName (..),
  )
where

import Aegle.Prelude
import Data.Text qualified as T
import Flat
import Prettyprinter

--------------------------------------------------------------------------------
-- Names

-- | De Bruijn indices
newtype Index = Index Int
  deriving stock (Generic)
  deriving newtype (Num, Eq, Ord, Show, Hashable, Enum, Flat, NFData)

-- | De Bruijn levels
newtype Level = Level Int
  deriving stock (Generic)
  deriving newtype (Eq, Ord, Num, Show, Hashable, Enum, Flat, NFData)

-- | Names
newtype Name = Name T.Text
  deriving stock (Generic)
  deriving newtype (Eq, Ord, Show, Hashable, IsString, Flat, NFData, Pretty)

-- | Module names
newtype ModuleName = ModuleName T.Text
  deriving stock (Generic)
  deriving newtype (Eq, Ord, Show, Hashable, IsString, Flat, NFData, Pretty)

-- | Library names
newtype LibName = LibName T.Text
  deriving stock (Generic)
  deriving newtype (Eq, Ord, Show, Hashable, IsString, Flat, NFData, Pretty)

-- | Fully-qualified names
data QName = QName
  { libName :: LibName,
    moduleName :: ModuleName,
    name :: Name
  }
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (Hashable, Flat, NFData)

-- | Possibly-qualified names
data PQName
  = Unqual Name
  | Qual ModuleName Name
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (Flat, NFData)

instance IsString PQName where
  fromString = Unqual . fromString

--------------------------------------------------------------------------------
-- Prettyprinting

instance Pretty Index where
  pretty (Index i) = "@" <> pretty i

instance Pretty Level where
  pretty (Level l) = "#" <> pretty l

instance Pretty QName where
  pretty QName {..} =
    -- ';' is not allowed for Agda identifier
    pretty libName <> ";" <> pretty moduleName <> "." <> pretty name

instance Pretty PQName where
  pretty = \case
    Unqual x -> pretty x
    Qual m x -> pretty m <> "." <> pretty x
