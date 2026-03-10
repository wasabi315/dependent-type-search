module TypeSearch.Database.Common where

import Control.Applicative
import Control.Monad
import Data.ByteString qualified as BS
import Data.Text qualified as T
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromField hiding (Binary)
import Database.PostgreSQL.Simple.ToField
import TypeSearch.Common
import TypeSearch.Raw
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

-- | Return-sort feature.

--   Compatibility:
--     approxReturnSort(query) = Yes -> returnSort(item) in {Yes, May}
--     approxReturnSort(query) = No  -> returnSort(item) in {No, May}
--     approxReturnSort(query) = May -> returnSort(item) = May
--     approxReturnSort(query) = ?   -> returnSort(item) in {Yes, No, May}

--
--     may
--    /   \
--  yes   no
data ReturnSort
  = YesReturnSort
  | NoReturnSort
  | MayReturnSort
  deriving stock (Eq, Show)

instance ToField ReturnSort where
  toField x = toField tag
    where
      tag = case x of
        NoReturnSort -> (0 :: Int)
        YesReturnSort -> 1
        MayReturnSort -> 2

instance FromField ReturnSort where
  fromField f dat =
    fromField f dat >>= \case
      (0 :: Int) -> pure NoReturnSort
      1 -> pure YesReturnSort
      2 -> pure MayReturnSort
      _ -> empty

-- | Polymorphic feature.

--   Compatibility:
--     approxPolymorphic(query) = Yes     -> polymorphic(item) = Yes
--     approxPolymorphic(query) = No      -> polymorphic(item) in {No, Yes}
--     approxPolymorphic(query) = ?       -> polymorphic(item) in {No, Yes}

--     yes
--      |
--      no
data Polymorphic = YesPolymorphic | NoPolymorphic
  deriving stock (Eq, Show)

instance ToField Polymorphic where
  toField x = toField case x of
    YesPolymorphic -> (1 :: Int)
    NoPolymorphic -> 0

instance FromField Polymorphic where
  fromField f dat =
    fromField f dat >>= \case
      (1 :: Int) -> pure YesPolymorphic
      0 -> pure NoPolymorphic
      _ -> empty

infArity :: Int
infArity = 127

-- | Arity feature.

--   Compatibility:
--     approxArity(query) : arity at least
--     arity(item)        : actual arity
--     approxArity(query) <= arity(item)

--   0 < 1 < 2 < ... < ∞
data Arity = InfArity | Arity Int
  deriving stock (Eq, Show)

instance ToField Arity where
  toField ar = toField case ar of
    InfArity -> infArity
    Arity ar -> ar

instance FromField Arity where
  fromField f dat =
    fromField f dat >>= \ar -> pure if ar == infArity then InfArity else Arity ar

--------------------------------------------------------------------------------

data DbItem = DbItem
  { name_qual :: DbQName,
    name_unqual :: DbName,
    sig :: DbTerm,
    body :: Maybe DbTerm,
    return_sort :: ReturnSort,
    polymorphic :: Polymorphic,
    arity :: Arity
  }
  deriving stock (Generic)
  deriving anyclass (ToRow, FromRow)

saveManyItems :: Connection -> [DbItem] -> IO ()
saveManyItems conn items =
  void $
    executeMany
      conn
      "INSERT INTO library_items(name_qual,name_unqual,sig,body,return_sort,polymorphic,arity) VALUES (?,?,?,?,?,?,?)"
      items

fuzzySearchByName :: Connection -> String -> IO [(DbQName, DbTerm)]
fuzzySearchByName conn name = do
  rows :: [(DbQName, DbTerm, Float)] <- query conn "SELECT name_qual, sig, similarity(?, name_unqual) AS sml FROM library_items WHERE similarity(?, name_unqual) > 0.9 ORDER BY sml DESC" (name, name)
  pure $ map (\(x, a, _) -> (x, a)) rows

--------------------------------------------------------------------------------

rawHead :: Raw -> Raw
rawHead = \case
  RApp t _ -> rawHead t
  RPos t _ -> rawHead t
  t -> t

endsInSort :: Raw -> Maybe Bool
endsInSort = go []
  where
    go :: [Name] -> Raw -> Maybe Bool
    go ctx = \case
      RPos t _ -> go ctx t
      RPi x _ b -> go (x : ctx) b
      RU -> Just True
      RSigma {} -> Just False
      RVar {} -> Just False
      RApp {} -> Just False
      RProj1 {} -> Just False
      RProj2 {} -> Just False
      -- ill-typed
      RLam {} -> Nothing
      RPair {} -> Nothing

approxReturnSort :: Raw -> Maybe (Maybe ReturnSort)
approxReturnSort = go []
  where
    go :: [(Name, Raw)] -> Raw -> Maybe (Maybe ReturnSort)
    go ctx = \case
      RPos t _ -> go ctx t
      RPi x a b -> go ((x, a) : ctx) b
      RU -> Just (Just YesReturnSort)
      RSigma {} -> Just (Just NoReturnSort)
      RLam {} -> Nothing
      RPair {} -> Nothing
      RProj1 {} -> Just Nothing
      RProj2 {} -> Just Nothing
      t -> case rawHead t of
        RVar (Unqual (flip lookup ctx -> Just t)) ->
          endsInSort t >>= \case
            True -> Just (Just MayReturnSort)
            False -> Just Nothing
        RVar {} -> Just Nothing
        RLam {} -> Just Nothing
        RProj1 {} -> Just Nothing
        RProj2 {} -> Just Nothing
        RU -> Nothing
        RPi {} -> Nothing
        RSigma {} -> Nothing
        RPair {} -> Nothing
        RApp {} -> impossible
        RPos {} -> impossible

approxPolymorphic :: Raw -> Maybe Polymorphic
approxPolymorphic = \case
  RPos t _ -> approxPolymorphic t
  RPi _ a b ->
    endsInSort a >>= \case
      True -> Just YesPolymorphic
      False -> approxPolymorphic b
  _ -> Just NoPolymorphic

arityAtLeast :: Raw -> Maybe Arity
arityAtLeast = go [] 0
  where
    go :: [(Name, Raw)] -> Int -> Raw -> Maybe Arity
    go ctx acc = \case
      RPos t _ -> go ctx acc t
      RPi x a@(rawHead -> RVar (Unqual (flip lookup ctx -> Just t))) b ->
        endsInSort t >>= \case
          False -> go ((x, a) : ctx) (acc + 1) b
          True -> Just InfArity
      RPi x a b -> go ((x, a) : ctx) (acc + 1) b
      RSigma {} -> Just (Arity acc)
      RU -> Just (Arity acc)
      RLam {} -> Nothing
      RPair {} -> Nothing
      RProj1 {} -> Just (Arity acc)
      RProj2 {} -> Just (Arity acc)
      t -> case rawHead t of
        RVar (Unqual (flip lookup ctx -> Just t)) ->
          endsInSort t >>= \case
            True -> Just InfArity
            False -> Just (Arity acc)
        RVar {} -> Just (Arity acc)
        RLam {} -> Just (Arity acc)
        RProj1 {} -> Just (Arity acc)
        RProj2 {} -> Just (Arity acc)
        RU -> Nothing
        RPi {} -> Nothing
        RSigma {} -> Nothing
        RPair {} -> Nothing
        RApp {} -> impossible
        RPos {} -> impossible

filterByFeatures :: Connection -> Raw -> IO (Maybe [DbItem])
filterByFeatures conn a = do
  case features of
    Nothing -> pure Nothing
    Just feat -> do
      print feat
      Just
        <$> query
          conn
          "SELECT name_qual, name_unqual, sig, body, return_sort, polymorphic, arity FROM library_items WHERE (return_sort in ?) AND (polymorphic in ?) AND (arity >= ?)"
          feat
  where
    features = do
      rrs <- approxReturnSort a
      rpl <- approxPolymorphic a
      rar <- arityAtLeast a
      pure
        ( In case rrs of
            Nothing -> [YesReturnSort, NoReturnSort, MayReturnSort]
            Just YesReturnSort -> [YesReturnSort, MayReturnSort]
            Just NoReturnSort -> [NoReturnSort, MayReturnSort]
            Just MayReturnSort -> [MayReturnSort],
          In case rpl of
            YesPolymorphic -> [YesPolymorphic]
            NoPolymorphic -> [YesPolymorphic, NoPolymorphic],
          rar
        )
