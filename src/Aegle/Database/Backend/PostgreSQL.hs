{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE QuasiQuotes #-}

module Aegle.Database.Backend.PostgreSQL
  ( newDbBuilder,
    HealthCheck (..),
    DanglingExport (..),
    newDbReader,
    migrate,
  )
where

import Aegle.Core.Name
import Aegle.Core.Term
import Aegle.Database.Backend hiding (loadCandidates, resolveNames)
import Aegle.Prelude
import Aegle.Search.Feature
import Control.Foldl qualified as Foldl
import Data.ByteString qualified as BS
import Data.Int
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as M
import Data.Text qualified as T
import Data.Vector qualified as V
import Flat
import Hasql.Connection
import Hasql.Decoders qualified as Decoders
import Hasql.DynamicStatements.Snippet qualified as Snippet
import Hasql.DynamicStatements.Statement
import Hasql.Encoders qualified as Encoders
import Hasql.Executor qualified as Executor
import Hasql.Migration
import Hasql.Pipeline qualified as Pipeline
import Hasql.Session
import Hasql.Statement
import Hasql.TH
import Hasql.Transaction.Sessions
import Paths_aegle
import System.FilePath

--------------------------------------------------------------------------------
-- Migration

migrate :: Connection -> IO ()
migrate conn = void do
  dataDir <- getDataDir
  let migrationDir = dataDir </> "migration"
  migrationCmds <- loadMigrationsFromDirectory migrationDir
  flip run conn $ transactionNoRetry ReadCommitted Write do
    traverse runMigration (MigrationInitialization : migrationCmds)

--------------------------------------------------------------------------------
-- Types

data DbLibraryItemRow = DbLibraryItemRow
  { canonicalName :: T.Text,
    kind :: T.Text,
    signature :: BS.ByteString,
    originalSignature :: BS.ByteString,
    body :: Maybe BS.ByteString,
    arity :: Int16,
    arityHasVar :: Bool,
    polymorphic :: T.Text,
    resultHead :: T.Text,
    resultHeadTop :: Maybe T.Text,
    moduleName :: T.Text,
    position :: Int32
  }

data DbExportRow = DbExportRow
  { canonicalName :: T.Text,
    exportAsQual :: T.Text, -- includes lib name
    exportAsQual' :: T.Text, -- does not include lib name
    exportAsUnqual :: T.Text
  }

--------------------------------------------------------------------------------
-- Encode/decode

encodeQName :: QName -> T.Text
encodeQName (QName l m x) = coerce l <> ";" <> coerce m <> "." <> coerce x

decodeQName :: T.Text -> Either T.Text QName
decodeQName txt = do
  let (lib, txt') = second T.tail $ T.breakOn ";" txt
      (mod, name) = first T.init $ T.breakOnEnd "." txt'
  when (T.null mod || T.null name) do
    throwError $ "Bad QName: " <> txt
  pure $ QName (coerce lib) (coerce mod) (coerce name)

encodeQName' :: QName' -> T.Text
encodeQName' (QName' m x) = coerce m <> "." <> coerce x

decodeQName' :: T.Text -> Either T.Text QName'
decodeQName' txt = do
  let (mod, name) = first T.init $ T.breakOnEnd "." txt
  when (T.null mod || T.null name) do
    throwError $ "Bad QName: " <> txt
  pure $ QName' (coerce mod) (coerce name)

nonNullQName'Enc :: Encoders.NullableOrNot Encoders.Value QName'
nonNullQName'Enc = Encoders.nonNullable $ encodeQName' >$< Encoders.text

nonNullQNameDec :: Decoders.NullableOrNot Decoders.Value QName
nonNullQNameDec = Decoders.nonNullable $ Decoders.refine decodeQName Decoders.text

encodeDefKind :: DefKind -> T.Text
encodeDefKind = \case
  DKPostulate -> "Postulate"
  DKFunction -> "Function"
  DKDatatype -> "Datatype"
  DKRecord -> "Record"
  DKConstructor -> "Constructor"
  DKPrimitive -> "Primitive"

decodeDefKind :: T.Text -> Either T.Text DefKind
decodeDefKind = \case
  "Postulate" -> pure DKPostulate
  "Function" -> pure DKFunction
  "Datatype" -> pure DKDatatype
  "Record" -> pure DKRecord
  "Constructor" -> pure DKConstructor
  "Primitive" -> pure DKPrimitive
  txt -> throwError $ "Bad DefKind: " <> txt

nonNullDefKindDec :: Decoders.NullableOrNot Decoders.Value DefKind
nonNullDefKindDec = Decoders.nonNullable $ Decoders.refine decodeDefKind Decoders.text

encodeTerm :: Term -> BS.ByteString
encodeTerm = flat

decodeTerm :: BS.ByteString -> Either T.Text Term
decodeTerm bin =
  unflat bin ??% \exn ->
    "Bad flat binary: " <> T.pack (displayException exn)

nonNullTermDec :: Decoders.NullableOrNot Decoders.Value Term
nonNullTermDec = Decoders.nonNullable $ Decoders.refine decodeTerm Decoders.bytea

encodePolymorphic :: Polymorphic -> T.Text
encodePolymorphic = \case
  Monomorphic -> "Monomorphic"
  Polymorphic -> "Polymorphic"

nonNullPolymorphicEnc :: Encoders.NullableOrNot Encoders.Value Polymorphic
nonNullPolymorphicEnc = Encoders.nonNullable $ encodePolymorphic >$< Encoders.text

encodeResultHeadTag :: ResultHead n -> T.Text
encodeResultHeadTag = \case
  RHTop {} -> "Top"
  RHU -> "U"
  RHVar -> "Var"
  RHSigma -> "Sigma"
  RHProj1 -> "Proj1"
  RHProj2 -> "Proj2"

encodeResultHeadTop :: ResultHead QName -> Maybe T.Text
encodeResultHeadTop = \case
  RHTop name -> Just $ encodeQName name
  _ -> Nothing

nonNullResultHeadTagEnc :: Encoders.NullableOrNot Encoders.Value (ResultHead n)
nonNullResultHeadTagEnc = Encoders.nonNullable $ encodeResultHeadTag >$< Encoders.text

--------------------------------------------------------------------------------
-- Build operation

newDbBuilder :: Connection -> DbBuilder IO HealthCheck
newDbBuilder conn = Foldl.FoldM step begin done
  where
    begin = orThrow $ flip run conn do
      sql "TRUNCATE library_items, exports RESTART IDENTITY;"

    step () LibraryFragment {..} = orThrow $ flip run conn $ pipeline do
      Pipeline.statement definitions insertManyDefinitions
        *> Pipeline.statement exports insertManyExports

    done () = orThrow $ flip run conn do
      sql
        """
        REFRESH MATERIALIZED VIEW exports_unqual;
        REFRESH MATERIALIZED VIEW exports_qual;
        """
      healthCheck

insertManyDefinitions :: Statement [Definition] ()
insertManyDefinitions = lmap encodeDefinitions do
  [resultlessStatement|
    INSERT INTO library_items
      ( canonical_name
      , kind
      , signature
      , original_signature
      , body
      , arity
      , arity_has_var
      , polymorphic
      , result_head
      , result_head_top
      , module_name
      , position )
    SELECT * FROM UNNEST
      ( $1 :: text[]
      , $2 :: text[] :: kind[]
      , $3 :: bytea[]
      , $4 :: bytea[]
      , $5 :: bytea?[]
      , $6 :: int2[]
      , $7 :: boolean[]
      , $8 :: text[] :: polymorphic[]
      , $9 :: text[] :: result_head[]
      , $10 :: text?[]
      , $11 :: text[]
      , $12 :: int[] )
  |]
  where
    encodeDefinitions = unzip12 . V.map (adapt . encodeDefinition) . V.fromList
    adapt DbLibraryItemRow {..} =
      ( canonicalName,
        kind,
        signature,
        originalSignature,
        body,
        arity,
        arityHasVar,
        polymorphic,
        resultHead,
        resultHeadTop,
        moduleName,
        position
      )

insertManyExports :: Statement [Export] ()
insertManyExports = lmap encodeExports do
  [resultlessStatement|
    INSERT INTO exports
      ( canonical_name
      , export_as_qual
      , export_as_qual_
      , export_as_unqual )
    SELECT * FROM UNNEST
      ( $1 :: text[]
      , $2 :: text[]
      , $3 :: text[]
      , $4 :: text[] )
  |]
  where
    encodeExports = V.unzip4 . V.map (adapt . encodeExport) . V.fromList
    adapt DbExportRow {..} =
      ( canonicalName,
        exportAsQual,
        exportAsQual',
        exportAsUnqual
      )

encodeDefinition :: Definition -> DbLibraryItemRow
encodeDefinition def = DbLibraryItemRow {..}
  where
    canonicalName = encodeQName def.name
    kind = encodeDefKind def.kind
    signature = encodeTerm def.signature
    originalSignature = encodeTerm def.originalSignature
    body = encodeTerm <$> def.body
    arity = fromIntegral def.feature.arity.arity
    arityHasVar = def.feature.arity.hasVar
    polymorphic = encodePolymorphic def.feature.polymorphic
    resultHead = encodeResultHeadTag def.feature.resultHead
    resultHeadTop = encodeResultHeadTop def.feature.resultHead
    moduleName = coerce def.moduleName
    position = fromIntegral def.position

encodeExport :: Export -> DbExportRow
encodeExport export = DbExportRow {..}
  where
    canonicalName = encodeQName export.canonicalName
    exportAsQual = encodeQName export.exportAs
    exportAsQual' = encodeQName' (ignoreLibName export.exportAs)
    exportAsUnqual = coerce export.exportAs.name

-- Health check

healthCheck :: Session HealthCheck
healthCheck = do
  danglingExports <- statement () loadDanglingExports
  pure HealthCheck {..}

newtype HealthCheck = HealthCheck
  { danglingExports :: V.Vector DanglingExport
  }

data DanglingExport = DanglingExport
  { exportAsQual :: QName,
    canonicalName :: QName
  }

loadDanglingExports :: Statement () (V.Vector DanglingExport)
loadDanglingExports =
  refineResult
    (traverse $ fmap (uncurry DanglingExport) . bitraverse decodeQName decodeQName)
    [vectorStatement|
      SELECT e.export_as_qual :: text, e.canonical_name :: text
      FROM exports e
      WHERE NOT EXISTS (
        SELECT 1
        FROM library_items i
        WHERE i.canonical_name = e.canonical_name
      )
    |]

--------------------------------------------------------------------------------
-- Read operation

newDbReader ::
  (Exception (Executor.Error a), Executor.Executor a) =>
  a -> DbReader IO
newDbReader exe =
  DbReader
    { resolveNames = resolveNames exe,
      loadCandidates = loadCandidates exe
    }

resolveNames ::
  (Traversable t, Exception (Executor.Error a), Executor.Executor a) =>
  a -> t PQName -> IO (t [Referent])
resolveNames exe names = do
  let names' = toList names
      (qualNames, unqualNames) = partitionEithers $ pqNameToEither <$> names'
  -- TODO: Better exception handling
  (resolQual, resolUnqual) <- orThrow $ Executor.execute exe $ pipeline do
    liftA2
      (,)
      do Pipeline.statement qualNames loadReferentQual
      do Pipeline.statement unqualNames loadReferentUnqual
  pure $! flip fmapDefault names \case
    Qual m x -> M.findWithDefault [] (QName' m x) resolQual
    Unqual x -> M.findWithDefault [] x resolUnqual

loadReferentQual :: Statement [QName'] (M.Map QName' [Referent])
loadReferentQual = lmap encodeQNames $ refineResult decodeReferents do
  [foldStatement|
    SELECT e.export_as_qual_ :: text, e.canonical_name :: text, i.body :: bytea?
    FROM library_items i
    JOIN exports_qual e
      ON i.canonical_name = e.canonical_name
    WHERE e.export_as_qual_ = ANY($1 :: text[])
  |]
    groupReferents
  where
    encodeQNames = V.map encodeQName' . V.fromList
    decodeReferents =
      traverse (traverse decodeReferent)
        . M.mapKeysMonotonic (fromRight (impossible "loadReferentQual.decodeReferents") . decodeQName')
    groupReferents =
      lmap (\(exportAs, canonName, body) -> (exportAs, (canonName, body))) do
        Foldl.foldByKeyMap Foldl.list

loadReferentUnqual :: Statement [Name] (M.Map Name [Referent])
loadReferentUnqual = lmap encodeNames $ refineResult decodeReferents do
  [foldStatement|
    SELECT e.export_as_unqual :: text, e.canonical_name :: text, i.body :: bytea?
    FROM library_items i
    JOIN exports_unqual e
      ON i.canonical_name = e.canonical_name
    WHERE e.export_as_unqual = ANY($1 :: text[])
  |]
    groupReferents
  where
    encodeNames = coerce @_ @(V.Vector T.Text) . V.fromList
    decodeReferents = traverse (traverse decodeReferent)
    groupReferents =
      lmap (\(exportAs, canonName, body) -> (coerce exportAs, (canonName, body))) do
        Foldl.foldByKeyMap Foldl.list

decodeReferent :: (T.Text, Maybe BS.ByteString) -> Either T.Text Referent
decodeReferent (canonicalName, body) = do
  canonicalName <- decodeQName canonicalName
  body <- traverse decodeTerm body
  pure $! Referent {..}

loadCandidates ::
  (Exception (Executor.Error a), Executor.Executor a) =>
  a -> [T.Text] -> [Compat (FilterFeature PQName)] -> IO [LibraryItem]
loadCandidates exe names compats = case NE.nonEmpty compats of
  Nothing -> pure []
  Just compats -> loadCandidatesNE exe names compats

loadCandidatesNE ::
  (Exception (Executor.Error a), Executor.Executor a) =>
  a -> [T.Text] -> NE.NonEmpty (Compat (FilterFeature PQName)) -> IO [LibraryItem]
loadCandidatesNE a names compats =
  -- TODO: Better exception handling
  orThrow $ Executor.execute a do
    statement () $ dynamicallyParameterized snippet decoder False
  where
    snippet =
      """
      SELECT
        i.canonical_name,
        i.kind,
        i.signature,
        i.original_signature,
        COALESCE (e.reexported_as, '{}') :: text[] AS reexported_as,
        i.module_name,
        i.position
      FROM library_items i
      LEFT JOIN (
        SELECT
          canonical_name,
          array_agg(DISTINCT export_as_qual)
            FILTER (
              WHERE export_as_qual IS NOT NULL
                AND export_as_qual <> canonical_name
            ) AS reexported_as
        FROM exports_qual
        GROUP BY canonical_name
      ) e
        ON e.canonical_name = i.canonical_name
      WHERE
      """
        <> parS (featuresSnippet compats)
        <> namesSnippet names

    namesSnippet names = case NE.nonEmpty names of
      Nothing -> mempty
      Just names ->
        """
        AND EXISTS (
          SELECT 1
          FROM exports_unqual eu
          WHERE
            eu.canonical_name = i.canonical_name AND
        """
          <> andS (nameSnippet <$> names)
          <> ")"

    nameSnippet name =
      "STRPOS(eu.export_as_unqual, "
        <> Snippet.param @T.Text name
        <> ") > 0"

    featuresSnippet = orS . fmap featureSnippet

    featureSnippet FilterFeatureCompat {..} =
      andS
        $ aritySnippet arity
        NE.:| catMaybes
          [ polymorphicSnippet polymorphic,
            resultHeadSnippet resultHead
          ]

    polymorphicSnippet = \case
      AnyPoly -> Nothing
      IsPoly ->
        Just
          $ "polymorphic = "
          <> parS
            ( do
                Snippet.encoderAndParam nonNullPolymorphicEnc Polymorphic
                  <> " :: polymorphic"
            )

    aritySnippet = \case
      HasVar -> "arity_has_var"
      HasVarOrGe arity ->
        orS
          [ "arity_has_var",
            "arity >= " <> Snippet.param @Int16 (fromIntegral arity)
          ]

    resultHeadSnippet = \case
      IsVar -> Just isVar
      IsVarOrU -> Just $ isVarOr RHU
      IsVarOrSigma -> Just $ isVarOr RHSigma
      IsVarOrProj1 -> Just $ isVarOr RHProj1
      IsVarOrProj2 -> Just $ isVarOr RHProj2
      IsVarOrTop n -> Just $ orS [isVar, isTop n]
      where
        enc rh =
          parS
            $ Snippet.encoderAndParam nonNullResultHeadTagEnc rh
            <> " :: result_head"

        var = enc RHVar
        isVar = "result_head = " <> var
        isVarOr rh = "result_head IN " <> listS [var, enc rh]
        isTop n =
          andS
            [ "result_head = " <> enc (RHTop ()),
              "result_head_top IN " <> topSnippet n
            ]

    topSnippet = \case
      Qual m x ->
        parS
          $ """
            SELECT canonical_name FROM exports_qual
            WHERE export_as_qual_ =
            """
          <> Snippet.encoderAndParam nonNullQName'Enc (QName' m x)
      Unqual x ->
        parS
          $ """
            SELECT canonical_name FROM exports_unqual
            WHERE export_as_unqual =
            """
          <> Snippet.param @T.Text (coerce x)

    decoder = Decoders.rowList do
      canonicalName <- Decoders.column nonNullQNameDec
      kind <- Decoders.column nonNullDefKindDec
      signature <- Decoders.column nonNullTermDec
      originalSignature <- Decoders.column nonNullTermDec
      reexportedAs <- Decoders.column $ Decoders.nonNullable $ Decoders.listArray nonNullQNameDec
      moduleName <- Decoders.column $ Decoders.nonNullable $ coerce Decoders.text
      position <- Decoders.column $ Decoders.nonNullable $ fromIntegral <$> Decoders.int4
      pure $! LibraryItem {..}

parS :: Snippet.Snippet -> Snippet.Snippet
parS s = "(" <> s <> ")"

orS :: NE.NonEmpty Snippet.Snippet -> Snippet.Snippet
orS ss = fmap parS ss `sepBy` " OR "

andS :: NE.NonEmpty Snippet.Snippet -> Snippet.Snippet
andS ss = fmap parS ss `sepBy` " AND "

listS :: NE.NonEmpty Snippet.Snippet -> Snippet.Snippet
listS ss = parS $ ss `sepBy` ", "

infix 3 `sepBy`

sepBy :: (Semigroup m) => NE.NonEmpty m -> m -> m
sepBy xs sep = sconcat (NE.intersperse sep xs)

--------------------------------------------------------------------------------
-- Utils

pqNameToEither :: PQName -> Either QName' Name
pqNameToEither = \case
  Qual m x -> Left (QName' m x)
  Unqual x -> Right x

unzip12 ::
  V.Vector (a, b, c, d, e, f, g, h, i, j, k, l) ->
  ( V.Vector a,
    V.Vector b,
    V.Vector c,
    V.Vector d,
    V.Vector e,
    V.Vector f,
    V.Vector g,
    V.Vector h,
    V.Vector i,
    V.Vector j,
    V.Vector k,
    V.Vector l
  )
unzip12 xs =
  ( V.map (\(a, _, _, _, _, _, _, _, _, _, _, _) -> a) xs,
    V.map (\(_, b, _, _, _, _, _, _, _, _, _, _) -> b) xs,
    V.map (\(_, _, c, _, _, _, _, _, _, _, _, _) -> c) xs,
    V.map (\(_, _, _, d, _, _, _, _, _, _, _, _) -> d) xs,
    V.map (\(_, _, _, _, e, _, _, _, _, _, _, _) -> e) xs,
    V.map (\(_, _, _, _, _, f, _, _, _, _, _, _) -> f) xs,
    V.map (\(_, _, _, _, _, _, g, _, _, _, _, _) -> g) xs,
    V.map (\(_, _, _, _, _, _, _, h, _, _, _, _) -> h) xs,
    V.map (\(_, _, _, _, _, _, _, _, i, _, _, _) -> i) xs,
    V.map (\(_, _, _, _, _, _, _, _, _, j, _, _) -> j) xs,
    V.map (\(_, _, _, _, _, _, _, _, _, _, k, _) -> k) xs,
    V.map (\(_, _, _, _, _, _, _, _, _, _, _, l) -> l) xs
  )
{-# INLINE unzip12 #-}
