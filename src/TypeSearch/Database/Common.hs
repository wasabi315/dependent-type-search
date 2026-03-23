module TypeSearch.Database.Common where

import Control.Exception
import Control.Monad
import Data.ByteString qualified as BS
import Data.Data (Typeable)
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

newtype a `As` b = As a
  deriving newtype (Show, Eq, Ord)

instance (Coercible a b, ToField b) => ToField (a `As` b) where
  toField x = toField @b (coerce x)

instance (Coercible a b, FromField b) => FromField (a `As` b) where
  fromField f dat = coerce (fromField @b f dat)

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
          "Flat deserialisation error: " ++ displayException e

type DbName = Name `As` T.Text

type DbModuleName = ModuleName `As` T.Text

type DbTerm = ViaFlat Term

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
data ReturnSort
  = YesReturnSort
  | NoReturnSort
  | MayReturnSort
  deriving stock (Eq, Show, Enum)
  deriving (ToField, FromField) via ViaEnum ReturnSort

-- | Polymorphic feature.
data Polymorphic = NoPolymorphic | YesPolymorphic
  deriving stock (Eq, Ord, Show, Enum)
  deriving (ToField, FromField) via ViaEnum Polymorphic

infArity :: Int
infArity = 127

-- | Arity feature.
data Arity = Arity Int | InfArity
  deriving stock (Eq, Show, Ord)

instance ToField Arity where
  toField ar = toField case ar of
    InfArity -> infArity
    Arity ar -> ar

instance FromField Arity where
  fromField f dat =
    fromField f dat >>= \ar -> pure $! if ar == infArity then InfArity else Arity ar

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
      (In quals, In (unquals :: [DbName]))
  let bcs =
        M.fromListWith (<>) $
          map
            (\(_, n, bc) -> maybe (n, BCCanonish) ((n,) . BCNames . S.fromList . map (\(DbQName (QName _ x)) -> coerce x) . fromPGArray) bc)
            res
      resol =
        M.fromListWith (++) $
          map
            (\(DbQName x, y, _) -> (coerce y, [x]))
            res
  pure (bcs, resol)
  where
    (quals, unquals) = partitionEithers $ map (\case Unqual x -> Right (As x); Qual m x -> Left (DbQName (QName m x))) $ S.toList (freeVars a)

type ReturnSortBodyMap = M.Map DbName (Maybe ReturnSort, Maybe [Bool])

fetchReturnSortBody :: Connection -> Raw -> IO ReturnSortBodyMap
fetchReturnSortBody conn a = do
  res :: [(DbName, Maybe ReturnSort, Maybe (PGArray Bool))] <-
    query
      conn
      "SELECT DISTINCT name_unqual, return_sort_body, occurrence FROM library_items WHERE name_qual in ? UNION SELECT DISTINCT name_unqual, return_sort_body, occurrence FROM library_items WHERE name_unqual in ?"
      (In quals, In (unquals :: [DbName]))
  pure $! flip M.fromListWith (map (\(x, y, z) -> (x, (y, fromPGArray <$> z))) res) \(rs1, occ1) (rs2, occ2) ->
    ( case (rs1, rs2) of
        (Just rs1, Just rs2) | rs1 == rs2 -> Just rs1
        _ -> Nothing,
      case (occ1, occ2) of
        (Just occ1, Just occ2) | occ1 == occ2 -> Just occ1
        _ -> Nothing
    )
  where
    (quals, unquals) = partitionEithers $ map (\case Unqual x -> Right (As x); Qual m x -> Left (DbQName (QName m x))) $ S.toList (freeVars a)

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
    ( \(tenv, resol) (DbQName x, ViaFlat t) -> do
        let tenv' = HML.insert x (eval emptyMetaCtx mempty [] t) tenv
            resol' = M.insertWith (++) x.name [x] resol
        pure (tenv', resol')
    )
