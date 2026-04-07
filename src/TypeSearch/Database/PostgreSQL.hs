module TypeSearch.Database.PostgreSQL where

import Control.Monad
import Data.Either
import Data.HashMap.Lazy qualified as HML
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Data.Traversable (for)
import Database.PostgreSQL.Simple
import TypeSearch.Common
import TypeSearch.Database.Feature
import TypeSearch.Evaluation
import TypeSearch.Raw
import TypeSearch.Term

--------------------------------------------------------------------------------

data DbItem = DbItem
  { name_qual :: QName,
    name_unqual :: Name,
    modul :: ModuleName,
    sig :: Term,
    body :: Maybe Term,
    return_type_head :: ReturnTypeHead QName,
    polymorphic :: Polymorphic,
    arity :: Int,
    arity_has_var :: Bool
  }
  deriving stock (Generic)
  deriving anyclass (ToRow, FromRow)

saveManyItems :: Connection -> [DbItem] -> IO ()
saveManyItems conn items =
  void $
    executeMany
      conn
      "INSERT INTO library_items(name_qual,name_unqual,module,sig,body,return_type_head,polymorphic,arity,arity_has_var) VALUES (?,?,?,?,?,?,?,?,?)"
      items

fuzzySearchByName :: Connection -> String -> IO [(QName, Term)]
fuzzySearchByName conn name = do
  rows :: [(QName, Term, Float)] <- query conn "SELECT name_qual, sig, similarity(?, name_unqual) AS sml FROM library_items WHERE similarity(?, name_unqual) > 0.9 ORDER BY sml DESC" (name, name)
  pure $ map (\(x, a, _) -> (x, a)) rows

fetchResolution :: Connection -> Raw -> IO (M.Map Name [QName])
fetchResolution conn a = do
  res :: [(QName, Name)] <-
    query
      conn
      "SELECT DISTINCT name_qual, name_unqual FROM library_items WHERE name_qual in ? UNION SELECT DISTINCT name_qual, name_unqual FROM library_items WHERE name_unqual in ?"
      (In quals, In (unquals :: [Name]))
  let resol =
        M.fromListWith (++) $
          map
            (\(x, y) -> (y, [x]))
            res
  pure resol
  where
    (quals, unquals) = partitionEithers $ map (\case Unqual x -> Right x; Qual m x -> Left (QName m x)) $ S.toList (rawFreeVars a)

filterByFeatures :: Connection -> S.Set QName -> Raw -> IO (Maybe [DbItem])
filterByFeatures conn aliasSet a = case computeReturnTypeHeadRaw aliasSet a of
  Nothing -> pure Nothing
  Just retType -> do
    let poly = case computePolymorphicRaw a of
          YesPolymorphic -> In [YesPolymorphic]
          NoPolymorphic -> In [NoPolymorphic, YesPolymorphic]
    let retType' = for retType \case
          Unqual x -> Left x
          Qual m x -> pure $ QName m x
    Just <$> case (retType', computeArityRaw a) of
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
      (Right ret, arity) ->
        query
          conn
          "SELECT name_qual, name_unqual, module, sig, body, return_type_head, polymorphic, arity, arity_has_var FROM library_items WHERE (polymorphic in ?) AND (arity_has_var OR arity = ?) AND (return_type_head in ?)"
          (poly, arity.arity, In [ret, RHVar])

fetchTopEnv :: Connection -> [QName] -> IO (TopEnv, M.Map Name [QName])
fetchTopEnv conn _candNames = do
  fold
    conn
    "SELECT name_qual, body FROM library_items WHERE body IS NOT NULL"
    ()
    (HML.empty, mempty)
    ( \(tenv, resol) (x, t) -> do
        let tenv' = HML.insert x (eval emptyMetaCtx mempty [] t) tenv
            resol' = M.insertWith (++) x.name [x] resol
        pure (tenv', resol')
    )
