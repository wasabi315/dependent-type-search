module TypeSearch.Database.Search
  ( search,
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
import TypeSearch.Database.PostgreSQL
import TypeSearch.Database.Search.Parser
import TypeSearch.Database.Search.Query qualified as Q
import TypeSearch.Prelude
import TypeSearch.Pretty
import TypeSearch.Unification

--------------------------------------------------------------------------------

search :: Connection -> S.Set QName -> IO ()
search conn transparentDefNames =
  evalReplOpts
    ReplOpts
      { banner = const $ pure ">> ",
        command = doSearch conn transparentDefNames,
        options = opts,
        prefix = Just ':',
        multilineCommand = Nothing,
        tabComplete = Word0 completer,
        initialiser = ini,
        finaliser = final
      }

type Repl = HaskelineT IO

opts :: Options Repl
opts =
  [ ("help", help)
  ]

help :: Command Repl
help _ =
  liftIO
    $ putStrLn
      """
      dependent-type-search

      Commands:
        :help          : show this help text
        <type>         : search for definitions by type
      """

ini :: Repl ()
ini = liftIO $ putStrLn "Welcome!"

final :: Repl ExitDecision
final = Exit <$ liftIO (putStrLn "Bye!")

completer :: (Monad m) => WordCompleter m
completer = listWordCompleter []

--------------------------------------------------------------------------------

doSearch :: Connection -> S.Set QName -> String -> Repl ()
doSearch conn transparentDefNames typ =
  either (liftIO . putStrLn) pure =<< runExceptT do
    typ <- parseQuery "interactive" (T.pack typ) ??% displayException
    feats <- computeFeatureQ transparentDefNames typ ??: "Ill-formed type"
    cands <- liftIO $ filterByFeatures conn feats
    resol1 <- liftIO $ fetchResolution conn typ
    (tenv, resol2) <- liftIO $ fetchTopEnv conn $ map (.nameQual) cands
    (result, time) <- liftIO $ timed $ typeSearch tenv (M.unionWith (++) resol1 resol2) typ cands
    let sorted = sortOn (\(TypeSearchResult _ _ _ _ sol) -> termSize sol) result
    liftIO $ displayTypeSearchResults cands sorted time

data TypeSearchResult = TypeSearchResult QName Type T.Text Iso Term

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
  for_ matches \(TypeSearchResult (QName m x) _ origA i sol) -> do
    putStrLn
      $ unlines
      $ concat
        [ [ showString "- " $ shows x $ showString " : " $ T.unpack origA,
            showString "  - module        : " $ shows m ""
          ],
          case i of
            Refl -> []
            i -> [showString "  - isomorphism   : " $ prettyIso 0 i ""],
          [ showString "  - solution      : " $ prettyTerm0 Unqualify sol ""
          ]
        ]
