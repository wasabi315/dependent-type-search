module TypeSearch.Database.Common where

import Data.ByteString qualified as BS
import Data.Text qualified as T
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromField hiding (Binary)
import Database.PostgreSQL.Simple.ToField
import Database.PostgreSQL.Simple.Types
import TypeSearch.Common
import TypeSearch.Term

--------------------------------------------------------------------------------

newtype DbName = DbName Name
  deriving newtype (Show)

instance ToField DbName where
  toField x = toField @T.Text (coerce x)

instance FromField DbName where
  fromField f dat = coerce <$> fromField @T.Text f dat

newtype DbQName = DbQName QName
  deriving newtype (Show)

instance ToField DbQName where
  toField (DbQName x) = toField (T.pack $ show x)

instance FromField DbQName where
  fromField f dat = do
    x <- fromField @T.Text f dat
    let xs = T.splitOn "." x
        m = coerce $ T.intercalate "." (init xs)
        f = coerce $ last xs
    pure $ DbQName (QName m f)

newtype DbTerm = DbTerm Term

instance ToField DbTerm where
  toField (DbTerm t) = toField (Binary $ flat t)

instance FromField DbTerm where
  fromField f dat = do
    Binary (x :: BS.ByteString) <- fromField f dat
    let Right t = unflat x
    pure (DbTerm t)

data DbItem = DbItem
  { name_qual :: DbQName,
    name_unqual :: DbName,
    used_top_names_qual :: PGArray DbQName,
    used_top_names_unqual :: PGArray DbName,
    sig :: DbTerm,
    body :: Maybe DbTerm
  }
  deriving stock (Generic)
  deriving anyclass (ToRow, FromRow)
