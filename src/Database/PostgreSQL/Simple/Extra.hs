module Database.PostgreSQL.Simple.Extra
  ( ViaEnum (..),
    ViaFlat (..),
  )
where

import Control.Exception
import Control.Monad
import Data.ByteString qualified as BS
import Data.Coerce
import Data.Typeable
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromField hiding (Binary)
import Database.PostgreSQL.Simple.ToField
import Flat
import Prelude

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
        returnError ConversionFailed f $
          "Flat deserialisation error: "
            ++ displayException e
