module TypeSearch.Common
  ( -- * DB
    ViaEnum (..),
    ViaFlat (..),

    -- * Names
    Index (..),
    Level (..),
    MetaVar (..),
    Name (..),
    ModuleName (..),
    QName (..),
    PQName (..),
    freshen,

    -- * Position
    SourcePos (..),
  )
where

import Control.Applicative
import Control.Exception
import Control.Monad
import Data.ByteString qualified as BS
import Data.Text qualified as T
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromField hiding (Binary)
import Database.PostgreSQL.Simple.ToField
import Flat
import Text.Megaparsec
import TypeSearch.Prelude

--------------------------------------------------------------------------------
-- Wrapper type for DB

-- | Store @Enum@ instance in @int@.
newtype ViaEnum a = ViaEnum a
  deriving newtype (Show, Eq, Ord)

instance (Enum a) => ToField (ViaEnum a) where
  toField (ViaEnum x) = toField (fromEnum x)

instance (Enum a) => FromField (ViaEnum a) where
  fromField f dat = coerce (toEnum @a <$!> fromField f dat)

-- | Store @Flat@ instance in @bytea@.
newtype ViaFlat a = ViaFlat a
  deriving newtype (Show, Eq, Ord)

instance (Flat a) => ToField (ViaFlat a) where
  toField (ViaFlat x) = toField (Binary $ flat x)

instance (Flat a, Typeable a) => FromField (ViaFlat a) where
  fromField f dat = coerce do
    Binary (x :: BS.ByteString) <- fromField f dat
    case unflat @a x of
      Right t -> pure t
      Left e ->
        returnError ConversionFailed f
          $ "Flat deserialisation error: "
          ++ displayException e

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
    let (m, f) = T.breakOnEnd "." x
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

freshen :: [Name] -> Name -> Name
freshen ns n
  | n `elem` ns = go 0
  | otherwise = n
  where
    go (i :: Int)
      | n' `notElem` ns = n'
      | otherwise = go (i + 1)
      where
        n' = Name $ coerce n <> T.pack (map subscript (show i))

subscript :: Char -> Char
subscript = \case
  '0' -> '₀'
  '1' -> '₁'
  '2' -> '₂'
  '3' -> '₃'
  '4' -> '₄'
  '5' -> '₅'
  '6' -> '₆'
  '7' -> '₇'
  '8' -> '₈'
  '9' -> '₉'
  c -> c
