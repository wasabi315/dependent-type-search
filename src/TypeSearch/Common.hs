module TypeSearch.Common
  ( -- * Names
    Index (..),
    Level (..),
    MetaVar (..),
    Name (..),
    ModuleName (..),
    QName (..),
    PQName (..),
  )
where

import Control.Applicative
import Data.Text qualified as T
import Database.PostgreSQL.Simple.FromField hiding (Binary)
import Database.PostgreSQL.Simple.ToField
import Flat
import TypeSearch.Prelude

--------------------------------------------------------------------------------
-- Names

-- | De Bruijn indices
newtype Index = Index Int
  deriving newtype (Num, Eq, Ord, Show, Hashable, Enum, Flat)

-- | De Bruijn levels
newtype Level = Level Int
  deriving newtype (Eq, Ord, Num, Show, Hashable, Flat)

-- | Metavariables
newtype MetaVar = MetaVar Int
  deriving newtype (Num, Eq, Ord, Hashable, Enum, Flat)

instance Show MetaVar where
  showsPrec _ (MetaVar m) = showString "?G%" . shows m

-- | Names
newtype Name = Name T.Text
  deriving newtype (Eq, Ord, Hashable, IsString, Flat, ToJSON, FromJSON, ToField, FromField)

instance Show Name where
  showsPrec _ (Name n) = showString (T.unpack n)

-- | Module names
newtype ModuleName = ModuleName T.Text
  deriving newtype (Eq, Ord, Hashable, IsString, Flat, ToJSON, FromJSON, ToField, FromField)

instance Show ModuleName where
  showsPrec _ (ModuleName n) = showString (T.unpack n)

-- | Qualified names
data QName = QName
  { moduleName :: ModuleName,
    name :: Name
  }
  deriving stock (Eq, Ord, Generic)
  deriving anyclass (Hashable, Flat, ToJSON, FromJSON)

instance Show QName where
  showsPrec _ x = shows x.moduleName . showChar '.' . shows x.name

instance ToField QName where
  toField x = toField (T.pack $ show x)

instance FromField QName where
  fromField f dat = do
    x <- fromField @T.Text f dat
    let (m, f) = first T.init $ T.breakOnEnd "." x
    pure $ QName (coerce m) (coerce f)

-- | Possibly qualified names
data PQName
  = Unqual Name
  | Qual ModuleName Name
  deriving stock (Eq, Ord, Generic)
  deriving anyclass (ToJSON, FromJSON)

instance IsString PQName where
  fromString = Unqual . Name . fromString

instance Show PQName where
  showsPrec _ = \case
    Unqual n -> shows n
    Qual m n -> shows m . showChar '.' . shows n
