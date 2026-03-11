module TypeSearch.Database.Common where

import Control.Applicative
import Control.Monad
import Data.ByteString qualified as BS
import Data.Either (partitionEithers)
import Data.HashMap.Lazy qualified as HML
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.FromField hiding (Binary)
import Database.PostgreSQL.Simple.Newtypes
import Database.PostgreSQL.Simple.ToField
import Database.PostgreSQL.Simple.Types
import TypeSearch.Common
import TypeSearch.Evaluation
import TypeSearch.Raw
import TypeSearch.Term

--------------------------------------------------------------------------------
-- Wrapper types for DB

newtype DbName = DbName Name
  deriving newtype (Show, Eq, Ord)

instance ToField DbName where
  toField x = toField @T.Text (coerce x)

instance FromField DbName where
  fromField f dat = coerce <$> fromField @T.Text f dat

newtype DbModuleName = DbModuleName ModuleName
  deriving newtype (Show, Eq, Ord)

instance ToField DbModuleName where
  toField x = toField @T.Text (coerce x)

instance FromField DbModuleName where
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

data ReturnTypeHead
  = RHSort
  | RHVar
  | RHFormer Name
  | RHOther
  deriving stock (Eq, Ord, Show, Generic)
  deriving anyclass (ToJSON, FromJSON)
  deriving (ToField, FromField) via Aeson ReturnTypeHead

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
    modul :: DbModuleName,
    sig :: DbTerm,
    body :: Maybe DbTerm,
    occurrence :: Maybe (PGArray Bool),
    noncanonish :: PGArray DbName,
    canonish :: PGArray DbName,
    return_type_head :: ReturnTypeHead,
    return_type_canonish :: PGArray DbName,
    polymorphic :: Polymorphic,
    arity :: Arity,
    return_sort_body :: Maybe ReturnSort,
    body_canonish :: Maybe (PGArray DbName)
  }
  deriving stock (Generic)
  deriving anyclass (ToRow, FromRow)

saveManyItems :: Connection -> [DbItem] -> IO ()
saveManyItems conn items =
  void $
    executeMany
      conn
      "INSERT INTO library_items(name_qual,name_unqual,module,sig,body,occurrence,noncanonish,canonish,return_type_head,return_type_canonish,polymorphic,arity,return_sort_body,body_canonish) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)"
      items

fuzzySearchByName :: Connection -> String -> IO [(DbQName, DbTerm)]
fuzzySearchByName conn name = do
  rows :: [(DbQName, DbTerm, Float)] <- query conn "SELECT name_qual, sig, similarity(?, name_unqual) AS sml FROM library_items WHERE similarity(?, name_unqual) > 0.9 ORDER BY sml DESC" (name, name)
  pure $ map (\(x, a, _) -> (x, a)) rows

--------------------------------------------------------------------------------

freeVars :: Raw -> S.Set PQName
freeVars = \case
  RVar x -> S.singleton x
  RU -> S.empty
  RPi x a b -> S.delete (Unqual x) $ freeVars a <> freeVars b
  RLam x t -> S.delete (Unqual x) $ freeVars t
  RApp t u -> freeVars t <> freeVars u
  RSigma x a b -> S.delete (Unqual x) $ freeVars a <> freeVars b
  RPair t u -> freeVars t <> freeVars u
  RProj1 t -> freeVars t
  RProj2 t -> freeVars t
  RPos t _ -> freeVars t

returnTypeFreeVars :: Raw -> S.Set DbName
returnTypeFreeVars = \case
  RPi x _ b -> S.delete (coerce x) $ returnTypeFreeVars b
  RPos t _ -> returnTypeFreeVars t
  t -> S.map (\case (Unqual x) -> coerce x; (Qual _ x) -> coerce x) $ freeVars t

data BodyCanonish
  = BCMixed
  | BCCanonish
  | BCNames (S.Set DbName)
  deriving stock (Show)

instance Semigroup BodyCanonish where
  BCCanonish <> BCCanonish = BCCanonish
  BCNames ns <> BCNames ns' = BCNames (S.intersection ns ns')
  _ <> _ = BCMixed

fetchBodyCanonish :: Connection -> Raw -> IO (M.Map DbName BodyCanonish, M.Map Name [QName])
fetchBodyCanonish conn a = do
  res :: [(DbQName, DbName, Maybe (PGArray DbQName))] <-
    query
      conn
      "SELECT DISTINCT name_qual, name_unqual, body_canonish FROM library_items WHERE name_qual in ? UNION SELECT DISTINCT name_qual, name_unqual, body_canonish FROM library_items WHERE name_unqual in ?"
      (In quals, In unquals)
  let bcs =
        M.fromListWith (<>) $
          map
            (\(_, n, bc) -> maybe (n, BCCanonish) ((n,) . BCNames . S.fromList . map (\(DbQName (QName _ x)) -> DbName x) . fromPGArray) bc)
            res
      resol =
        M.fromListWith (++) $
          map
            (\(DbQName x, DbName y, _) -> (y, [x]))
            res
  pure (bcs, resol)
  where
    (quals, unquals) = partitionEithers $ map (\case Unqual x -> Right (DbName x); Qual m x -> Left (DbQName (QName m x))) $ S.toList (freeVars a)

type ReturnSortBodyMap = M.Map DbName (Maybe ReturnSort, Maybe [Bool])

fetchReturnSortBody :: Connection -> Raw -> IO ReturnSortBodyMap
fetchReturnSortBody conn a = do
  res :: [(DbName, Maybe ReturnSort, Maybe (PGArray Bool))] <-
    query
      conn
      "SELECT DISTINCT name_unqual, return_sort_body, occurrence FROM library_items WHERE name_qual in ? UNION SELECT DISTINCT name_unqual, return_sort_body, occurrence FROM library_items WHERE name_unqual in ?"
      (In quals, In unquals)
  pure $! flip M.fromListWith (map (\(x, y, z) -> (x, (y, fromPGArray <$> z))) res) \(rs1, occ1) (rs2, occ2) ->
    ( case (rs1, rs2) of
        (Just rs1, Just rs2) | rs1 == rs2 -> Just rs1
        _ -> Nothing,
      case (occ1, occ2) of
        (Just occ1, Just occ2) | occ1 == occ2 -> Just occ1
        _ -> Nothing
    )
  where
    (quals, unquals) = partitionEithers $ map (\case Unqual x -> Right (DbName x); Qual m x -> Left (DbQName (QName m x))) $ S.toList (freeVars a)

rawHead :: Raw -> Raw
rawHead = \case
  RApp t _ -> rawHead t
  RPos t _ -> rawHead t
  t -> t

endsInSort :: ReturnSortBodyMap -> Raw -> Maybe Bool
endsInSort rsbm = go []
  where
    go :: [Name] -> Raw -> Maybe Bool
    go ctx = \case
      RPos t _ -> go ctx t
      RPi x _ b -> go (x : ctx) b
      RU -> Just True
      RSigma {} -> Just False
      RProj1 {} -> Just False
      RProj2 {} -> Just False
      -- ill-typed
      RLam {} -> Nothing
      RPair {} -> Nothing
      t -> case rawHead t of
        RVar (Unqual x) | x `elem` ctx -> Just False
        RVar (Unqual x) | Just (Just rs, _) <- M.lookup (coerce x) rsbm ->
          case rs of
            YesReturnSort -> Just True
            _ -> Just False
        RVar (Qual _ x) | Just (Just rs, _) <- M.lookup (coerce x) rsbm ->
          case rs of
            YesReturnSort -> Just True
            _ -> Just False
        _ -> Nothing

data ApproxReturnTypeHead
  = ARHVar
  | ARHSort
  | ARHFormer PQName
  | ARHUnknown

approxReturnTypeHead :: M.Map DbName BodyCanonish -> ReturnSortBodyMap -> Raw -> Maybe ApproxReturnTypeHead
approxReturnTypeHead bcs rsbm = go []
  where
    go ctx = \case
      RPos t _ -> go ctx t
      RPi x a b -> go ((x, a) : ctx) b
      RU -> Just ARHSort
      RSigma {} -> Just (ARHFormer (Qual "Agda.Builtin.Sigma" "Σ"))
      RLam {} -> Nothing
      RPair {} -> Nothing
      RProj1 {} -> Just ARHUnknown
      RProj2 {} -> Just ARHUnknown
      t -> case rawHead t of
        RVar (Unqual (flip lookup ctx -> Just t)) ->
          endsInSort rsbm t >>= \case
            True -> Just ARHVar
            False -> Just ARHUnknown
        RVar (Unqual x) -> case M.lookup (coerce x) bcs of
          Nothing -> Nothing
          Just BCMixed -> Just ARHUnknown
          Just BCCanonish -> Just (ARHFormer (Unqual x))
          Just (BCNames _) -> Just ARHUnknown
        RVar (Qual m x) -> case M.lookup (coerce x) bcs of
          Nothing -> Nothing
          Just BCMixed -> Just ARHUnknown
          Just BCCanonish -> Just (ARHFormer (Qual m x))
          Just (BCNames _) -> Just ARHUnknown
        _ -> Just ARHUnknown

approxReturnSort :: ReturnSortBodyMap -> Raw -> Maybe (Maybe ReturnSort)
approxReturnSort rsbm = go []
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
          endsInSort rsbm t >>= \case
            True -> Just (Just MayReturnSort)
            False -> Just Nothing
        RVar (Unqual x) -> case M.lookup (coerce x) rsbm of
          Nothing -> Nothing
          Just (Nothing, _) -> Just Nothing
          Just (Just MayReturnSort, _) -> Just Nothing
          Just (Just YesReturnSort, _) -> Just (Just YesReturnSort)
          Just (Just NoReturnSort, _) -> Just (Just NoReturnSort)
        RVar (Qual _ x) -> case M.lookup (coerce x) rsbm of
          Nothing -> Nothing
          Just (Nothing, _) -> Just Nothing
          Just (Just MayReturnSort, _) -> Just Nothing
          Just (Just YesReturnSort, _) -> Just (Just YesReturnSort)
          Just (Just NoReturnSort, _) -> Just (Just NoReturnSort)
        RLam {} -> Just Nothing
        RProj1 {} -> Just Nothing
        RProj2 {} -> Just Nothing
        RU -> Nothing
        RPi {} -> Nothing
        RSigma {} -> Nothing
        RPair {} -> Nothing
        RApp {} -> impossible
        RPos {} -> impossible

approxPolymorphic :: ReturnSortBodyMap -> Raw -> Maybe Polymorphic
approxPolymorphic rsbm = \case
  RPos t _ -> approxPolymorphic rsbm t
  RPi _ a b ->
    endsInSort rsbm a >>= \case
      True -> Just YesPolymorphic
      False -> approxPolymorphic rsbm b
  _ -> Just NoPolymorphic

arityAtLeast :: ReturnSortBodyMap -> Raw -> Maybe Arity
arityAtLeast rsbm = go [] 0
  where
    go :: [(Name, Raw)] -> Int -> Raw -> Maybe Arity
    go ctx acc = \case
      RPos t _ -> go ctx acc t
      RPi x a@(rawHead -> RVar (Unqual (flip lookup ctx -> Just t))) b ->
        endsInSort rsbm t >>= \case
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
          endsInSort rsbm t >>= \case
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

fetchAllItems :: Connection -> IO [DbItem]
fetchAllItems conn = do
  query
    conn
    "SELECT name_qual, name_unqual, module, sig, body, occurrence, noncanonish, canonish, return_type_head, return_type_canonish, polymorphic, arity, return_sort_body, body_canonish FROM library_items WHERE name_unqual = ?"
    (Only "foldr" :: Only String)

filterByFeatures :: Connection -> M.Map DbName BodyCanonish -> ReturnSortBodyMap -> Raw -> IO (Maybe [DbItem])
filterByFeatures conn bcs rsbm a = do
  case features of
    Nothing -> pure Nothing
    Just (rrh, rpl, rar) -> do
      -- print (rrh, rpl, rar)
      case rrh of
        Just rrh ->
          Just
            <$> query
              conn
              "SELECT name_qual, name_unqual, module, sig, body, occurrence, noncanonish, canonish, return_type_head, return_type_canonish, polymorphic, arity, return_sort_body, body_canonish FROM library_items WHERE (return_type_head in ?) AND (polymorphic in ?) AND (arity >= ?) AND (polymorphic = ? OR canonish @> ?) AND (polymorphic = ? OR return_type_canonish @> ?)"
              (rrh, rpl, rar, YesPolymorphic, PGArray (S.toList cs), YesPolymorphic, PGArray (S.toList rcs))
        Nothing ->
          Just
            <$> query
              conn
              "SELECT name_qual, name_unqual, module, sig, body, occurrence, noncanonish, canonish, return_type_head, return_type_canonish, polymorphic, arity, return_sort_body, body_canonish FROM library_items WHERE (polymorphic in ?) AND (arity >= ?) AND (polymorphic = ? OR canonish @> ?) AND (polymorphic = ? OR return_type_canonish @> ?)"
              (rpl, rar, YesPolymorphic, PGArray (S.toList cs), YesPolymorphic, PGArray (S.toList rcs))
  where
    cs = flip M.foldMapWithKey bcs \cases
      _ BCMixed -> S.empty
      x BCCanonish -> S.singleton x
      _ (BCNames xs) -> xs
    rcs = flip M.foldMapWithKey (M.restrictKeys bcs (coerce $ returnTypeFreeVars a)) \cases
      _ BCMixed -> S.empty
      x BCCanonish -> S.singleton x
      _ (BCNames xs) -> xs
    features = do
      rrh <- approxReturnTypeHead bcs rsbm a
      rpl <- approxPolymorphic rsbm a
      rar <- arityAtLeast rsbm a
      pure
        ( case rrh of
            ARHSort -> Just $ In [RHSort, RHVar]
            ARHVar -> Just $ In [RHVar]
            ARHFormer (Unqual x) -> Just $ In [RHFormer x, RHVar]
            ARHFormer (Qual _ x) -> Just $ In [RHFormer x, RHVar]
            ARHUnknown -> Nothing,
          In case rpl of
            YesPolymorphic -> [YesPolymorphic]
            NoPolymorphic -> [YesPolymorphic, NoPolymorphic],
          rar
        )

fetchTopEnv :: Connection -> [DbQName] -> IO (TopEnv, M.Map Name [QName])
fetchTopEnv conn candNames = do
  fold
    conn
    "SELECT name_qual, body FROM library_items WHERE body IS NOT NULL AND name_unqual in (SELECT DISTINCT unnest(noncanonish) FROM library_items WHERE name_qual in ?)"
    (Only (In candNames))
    (HML.empty, mempty)
    ( \(tenv, resol) (DbQName x, DbTerm t) -> do
        let tenv' = HML.insert x (eval emptyMetaCtx mempty [] t) tenv
            resol' = M.insertWith (++) x.name [x] resol
        pure (tenv', resol')
    )
