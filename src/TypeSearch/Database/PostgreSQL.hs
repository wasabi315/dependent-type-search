module TypeSearch.Database.PostgreSQL where

import Data.HashMap.Lazy qualified as HML
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Database.PostgreSQL.Simple as PSQL
import Database.PostgreSQL.Simple.Migration
import Paths_dependent_type_search
import System.FilePath
import TypeSearch.Core.Evaluation
import TypeSearch.Core.Name
import TypeSearch.Core.Term
import TypeSearch.Database.Feature
import TypeSearch.Database.Query qualified as Q
import TypeSearch.Prelude

--------------------------------------------------------------------------------

data DbItem = DbItem
  { nameQual :: QName,
    nameUnqual :: Name,
    modul :: ModuleName,
    sig :: Term,
    body :: Maybe Term,
    returnTypeHead :: ReturnTypeHead QName,
    polymorphic :: Polymorphic,
    arity :: Int,
    arityHasVar :: Bool
  }
  deriving stock (Generic)
  deriving anyclass (ToRow, FromRow)

migrate :: Connection -> IO ()
migrate conn = do
  migrationDir <- getDataDir <&> (</> "migration")
  void do
    runMigrations
      conn
      defaultOptions
      [MigrationInitialization, MigrationDirectory migrationDir]

saveManyItems :: Connection -> [DbItem] -> IO ()
saveManyItems conn items =
  void
    $ executeMany
      conn
      "INSERT INTO library_items(name_qual,name_unqual,module,sig,body,return_type_head,polymorphic,arity,arity_has_var) VALUES (?,?,?,?,?,?,?,?,?)"
      items

fetchResolution :: Connection -> Q.Term -> IO (M.Map Name [QName])
fetchResolution conn a = do
  res :: [(QName, Name)] <-
    query
      conn
      "SELECT DISTINCT name_qual, name_unqual FROM library_items WHERE name_qual in ? UNION SELECT DISTINCT name_qual, name_unqual FROM library_items WHERE name_unqual in ?"
      (In quals, In (unquals :: [Name]))
  let resol =
        M.fromListWith (++)
          $ map
            (\(x, y) -> (y, [x]))
            res
  pure resol
  where
    (quals, unquals) = partitionEithers $ map (\case Unqual x -> Right x; Qual m x -> Left (QName m x)) $ S.toList (Q.freeVars a)

filterByFeatures :: Connection -> Feature PQName -> IO [DbItem]
filterByFeatures conn (Feature {..}) = do
  let retType = for returnTypeHead \case
        Unqual x -> Left x
        Qual m x -> pure $ QName m x
      poly = case polymorphic of
        YesPolymorphic -> In [YesPolymorphic]
        NoPolymorphic -> In [NoPolymorphic, YesPolymorphic]
  case (retType, arity) of
    (Right RHUnknown, (.hasVar) -> True) ->
      query
        conn
        "SELECT name_qual, name_unqual, module, sig, body, return_type_head, polymorphic, arity, arity_has_var FROM library_items WHERE (polymorphic in ?) AND arity_has_var"
        (Only poly)
    (Right RHUnknown, arity) ->
      query
        conn
        "SELECT name_qual, name_unqual, module, sig, body, return_type_head, polymorphic, arity, arity_has_var FROM library_items WHERE (polymorphic in ?) AND (arity_has_var OR arity >= ?)"
        (poly, arity.arity)
    (Left x, (.hasVar) -> True) ->
      query
        conn
        "SELECT name_qual, name_unqual, module, sig, body, return_type_head, polymorphic, arity, arity_has_var FROM library_items WHERE (polymorphic in ?) AND arity_has_var AND ((return_type_head ->> 'tag' = 'RHVar') OR ((return_type_head ->> 'tag' = 'RHTop') AND (return_type_head #>> '{contents,name}' = ?)))"
        (poly, x)
    (Left x, arity) ->
      query
        conn
        "SELECT name_qual, name_unqual, module, sig, body, return_type_head, polymorphic, arity, arity_has_var FROM library_items WHERE (polymorphic in ?) AND (arity_has_var OR arity = ?) AND ((return_type_head ->> 'tag' = 'RHVar') OR ((return_type_head ->> 'tag' = 'RHTop') AND (return_type_head #>> '{contents,name}' = ?)))"
        (poly, arity.arity, x)
    (Right ret, (.hasVar) -> True) ->
      query
        conn
        "SELECT name_qual, name_unqual, module, sig, body, return_type_head, polymorphic, arity, arity_has_var FROM library_items WHERE (polymorphic in ?) AND arity_has_var AND (return_type_head in ?)"
        (poly, In [ret, RHVar])
    (Right ret, arity) -> do
      query
        conn
        "SELECT name_qual, name_unqual, module, sig, body, return_type_head, polymorphic, arity, arity_has_var FROM library_items WHERE (polymorphic in ?) AND (arity_has_var OR arity = ?) AND (return_type_head in ?)"
        (poly, arity.arity, In [ret, RHVar])

fetchTopEnv :: Connection -> [QName] -> IO TopEnv
fetchTopEnv conn _candNames = do
  PSQL.fold
    conn
    "SELECT name_qual, body FROM library_items WHERE body IS NOT NULL"
    ()
    HML.empty
    ( \tenv (x, t) -> do
        pure $! HML.insert x (eval emptyMetaCtx mempty [] t) tenv
    )
