module TypeSearch.Database.Search
  ( interactive,
    search,
  )
where

import Data.ImmatureStream qualified as ImS
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import Data.Time.Clock
import Database.PostgreSQL.Simple
import Streamly.Data.Stream.Prelude qualified as Streamly
import System.Console.Repline
import TypeSearch.Core.Evaluation
import TypeSearch.Core.Isomorphism
import TypeSearch.Core.Name
import TypeSearch.Core.Term
import TypeSearch.Database.Feature
import TypeSearch.Database.Parser
import TypeSearch.Database.PostgreSQL
import TypeSearch.Database.Query qualified as Q
import TypeSearch.Prelude
import TypeSearch.Pretty
import TypeSearch.Unification

--------------------------------------------------------------------------------

search :: Connection -> S.Set QName -> T.Text -> IO ()
search conn transparentDefNames typ =
  either putStrLn pure =<< runExceptT do
    typ <- parseQuery "interactive" typ ??% displayException
    feats <- featureQ transparentDefNames typ ??: "Ill-formed type"
    cands <- liftIO $ filterByFeatures conn feats
    resol <- liftIO $ fetchResolution conn typ
    tenv <- liftIO $ fetchTopEnv conn $ map (.nameQual) cands
    (result, time) <- liftIO $ timed $ typeSearch tenv resol typ cands
    let sorted = sortOn (termSize . (.solution)) result
    liftIO $ displayTypeSearchResults cands sorted time

-- Interactive search shell
interactive :: Connection -> S.Set QName -> IO ()
interactive conn transparentDefNames = evalReplOpts ReplOpts {..}
  where
    banner _ = pure ">> "
    command = liftIO . search conn transparentDefNames . T.pack
    prefix = Just ':'
    multilineCommand = Nothing
    tabComplete = Word0 (listWordCompleter [])
    initialiser = liftIO $ putStrLn "Welcome to dependent-type-search!"
    finaliser = liftIO $ Exit <$ putStrLn "Bye!"

    options = [("help", help)]
    help _ =
      liftIO
        $ putStrLn
          """
          Commands:
            :help          : show this help text
            <type>         : search for definitions by type

          """

--------------------------------------------------------------------------------

data TypeSearchResult = TypeSearchResult
  { name :: QName,
    sig :: Type,
    origSigText :: T.Text,
    iso :: Iso,
    solution :: Term
  }

typeSearch :: TopEnv -> M.Map Name [QName] -> Q.Type -> [DbItem] -> IO [TypeSearchResult]
typeSearch tenv resol query items = do
  let queries = Q.possibleResolutions resol query
  Streamly.toList
    $ Streamly.parConcatMap
      id
      ( \item ->
          case ImS.streamToMaybe $ foldMapA (\query -> typeSearchOne tenv query item) queries of
            Nothing -> Streamly.nil
            Just res -> Streamly.cons res Streamly.nil
      )
    $ Streamly.fromList items

typeSearchOne :: TopEnv -> Term -> DbItem -> ImS.Stream TypeSearchResult
typeSearchOne tenv query DbItem {sig, origSigText, nameQual = name} = do
  (i, inst) <- check name (initCtx tenv, Here) (eval emptyMetaCtx tenv [] query) (eval emptyMetaCtx tenv [] sig)
  pure (TypeSearchResult name sig origSigText i inst)

displayTypeSearchResults :: [DbItem] -> [TypeSearchResult] -> NominalDiffTime -> IO ()
displayTypeSearchResults cands matches time = do
  putStrLn $ shows (length matches) $ showString " item(s) matched in " $ shows (length cands) " candidate(s)"
  putStrLn $ showString "Took " $ shows time "\n"
  for_ matches \TypeSearchResult {name = QName {..}, ..} -> do
    putStrLn
      $ unlines
      $ concat
        [ [ showString "- " $ shows name $ showString " : " $ T.unpack origSigText,
            showString "  - module        : " $ shows moduleName ""
          ],
          case iso of
            Refl -> []
            i -> [showString "  - isomorphism   : " $ prettyIso 0 i ""],
          [ showString "  - solution      : " $ prettyTerm0 Unqualify solution ""
          ]
        ]
