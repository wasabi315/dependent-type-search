module TypeSearch.Database.Common where

import Control.Applicative
import Data.ByteString qualified as BS
import Data.Text qualified as T
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromField hiding (Binary)
import Database.PostgreSQL.Simple.ToField
import TypeSearch.Common
import TypeSearch.Term

--------------------------------------------------------------------------------
-- Wrapper types for DB

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

--------------------------------------------------------------------------------
-- Features

data ReturnSort
  = YesReturnSort
  | NoReturnSort
  | MayReturnSort
  deriving stock (Eq)

instance ToField ReturnSort where
  toField x = toField tag
    where
      tag = case x of
        YesReturnSort -> (0 :: Int)
        NoReturnSort -> 1
        MayReturnSort -> 2

instance FromField ReturnSort where
  fromField f dat =
    fromField f dat >>= \case
      (0 :: Int) -> pure YesReturnSort
      1 -> pure NoReturnSort
      2 -> pure MayReturnSort
      _ -> empty

data Polymorphic = YesPolymorphic | NoPolymorphic
  deriving stock (Eq)

instance ToField Polymorphic where
  toField x = toField tag
    where
      tag = case x of
        YesPolymorphic -> (0 :: Int)
        NoPolymorphic -> 1

instance FromField Polymorphic where
  fromField f dat =
    fromField f dat >>= \case
      (0 :: Int) -> pure YesPolymorphic
      1 -> pure NoPolymorphic
      _ -> empty

data Arity = InfArity | Arity Int
  deriving stock (Eq)

instance ToField Arity where
  toField ar = toField case ar of
    InfArity -> -1 :: Int
    Arity ar -> ar

instance FromField Arity where
  fromField f dat =
    fromField f dat >>= \ar -> pure if ar >= 0 then Arity ar else InfArity
