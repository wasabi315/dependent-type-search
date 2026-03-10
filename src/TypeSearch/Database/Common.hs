module TypeSearch.Database.Common where

import Control.Applicative
import Control.Monad
import Data.ByteString qualified as BS
import Data.Either (partitionEithers)
import Data.Set qualified as S
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

-- In agda-stdlib
--   yes : 2860
--   no  : 17067
--   may : 864
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

-- In agda-stdlib
--   yes : 11140
--   no  : 9651
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

-- In agda-stdlib
--   0 : 1514
--   1 : 1342
--   2 : 1943
--   3 : 2084
--   4 : 1736
--   5 : 1775
--   6 : 1728
--   7 : 1350
--   8 : 1103
--   9 : 850
--  10 : 522
--  11 : 430
--  12 : 255
--  13 : 215
--  14 : 188
--  15 : 123
--  16 : 74
--  17 : 49
--  18 : 60
--  19 : 18
--  20 : 22
--  21 : 4
--  22 : 9
--  23 : 13
--  24 : 0
--  25 : 22
--  26 : 1
--  27 : 1
--  28 : 2
--  29 : 0
--  30 : 0
--  31 : 0
--  32 : 1
--  33 : 0
--  34 : 0
--  35 : 0
--  36 : 2
--  ∞  : 3374
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

freeVars :: Raw -> S.Set PQName
freeVars = go []
  where
    go ctx = \case
      RVar (Unqual x) | x `elem` ctx -> S.empty
      RVar x -> S.singleton x
      RU -> S.empty
      RPi x a b -> go ctx a <> go (x : ctx) b
      RLam x t -> go (x : ctx) t
      RApp t u -> go ctx t <> go ctx u
      RSigma x a b -> go ctx a <> go (x : ctx) b
      RPair t u -> go ctx t <> go ctx u
      RProj1 t -> go ctx t
      RProj2 t -> go ctx t
      RPos t _ -> go ctx t

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

fetchEnv :: Connection -> Raw -> IO [DbItem]
fetchEnv conn a = do
  query
    conn
    "SELECT name_qual, name_unqual, sig, body, return_sort, polymorphic, arity FROM library_items WHERE name_qual in ? UNION SELECT name_qual, name_unqual, sig, body, return_sort, polymorphic, arity FROM library_items WHERE name_unqual in ?"
    (In quals, In unquals)
  where
    (quals, unquals) = partitionEithers $ map (\case Unqual x -> Right (DbName x); Qual m x -> Left (DbQName (QName m x))) $ S.toList (freeVars a)
