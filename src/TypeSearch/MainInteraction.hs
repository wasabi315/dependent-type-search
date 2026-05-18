module TypeSearch.MainInteraction (mainLoop) where

import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import Data.Time.Clock
import Database.PostgreSQL.Simple
import Stream
import Streamly.Data.Stream.Prelude qualified as Streamly
import System.Console.Haskeline
import TypeSearch.Common
import TypeSearch.Database.PostgreSQL
import TypeSearch.Evaluation
import TypeSearch.Parser
import TypeSearch.Prelude
import TypeSearch.Pretty
import TypeSearch.Raw
import TypeSearch.Term
import TypeSearch.Unification

--------------------------------------------------------------------------------

data Command
  = Continue
  | Help
  | Quit
  | SearchByName String
  | SearchByType String

parseCommand :: Maybe String -> Either String Command
parseCommand = maybe (pure Continue) \input -> case words input of
  [] -> pure Continue
  ":help" : _ -> pure Help
  ":h" : _ -> pure Help
  ":quit" : _ -> pure Quit
  ":q" : _ -> pure Quit
  (':' : cmd) : _ -> Left $ "Unknown command: " <> cmd
  "name" : name : _ -> pure $ SearchByName name
  "type" : rest -> pure $ SearchByType (unwords rest)
  search : _ -> Left $ "Unknown search: " <> search

helpText :: String
helpText =
  unlines
    [ "dependent-type-search",
      "",
      "Commands:",
      "  :help, :h      : show this help text",
      "  :quit, :q      : quit the program",
      "  <name>         : search for definitions whose name is similar to <name>",
      ""
    ]

mainLoop :: Connection -> S.Set QName -> IO ()
mainLoop conn transparentDefSet = runInputT defaultSettings go
  where
    go = do
      input <- getInputLine ">> "
      case parseCommand input of
        Left err -> do
          outputStrLn err
          go
        Right Continue -> go
        Right Help -> do
          outputStrLn helpText
          go
        Right Quit -> outputStrLn "Bye!"
        Right (SearchByName name) -> do
          items <- liftIO $ fuzzySearchByName conn name
          displaySearchByNameResult items
          go
        Right (SearchByType typ) -> case parseRaw "interactive" (T.pack typ) of
          Left err -> outputStrLn (displayException err) >> go
          Right typ -> do
            cands <- liftIO $ filterByFeatures conn transparentDefSet typ
            case cands of
              Nothing -> outputStrLn "Ill-formed type" >> go
              Just cands -> do
                -- outputStrLn $ show $ map (.name_unqual) cands
                resol1 <- liftIO $ fetchResolution conn typ
                (tenv, resol2) <- liftIO $ fetchTopEnv conn $ map (.name_qual) cands
                (result, time) <- liftIO $ timed $ typeSearch tenv (M.unionWith (++) resol1 resol2) typ cands
                let sorted = sortOn (\(TypeSearchResult _ _ _ _ sol) -> termSize sol) result
                displayTypeSearchResults cands sorted time
                go

timed :: IO a -> IO (a, NominalDiffTime)
timed a = do
  t1 <- getCurrentTime
  res <- a
  t2 <- getCurrentTime
  let diff = diffUTCTime t2 t1
  pure (res, diff)

data TypeSearchResult = TypeSearchResult QName Type T.Text Iso Term

typeSearch :: TopEnv -> M.Map Name [QName] -> Raw -> [DbItem] -> IO [TypeSearchResult]
typeSearch tenv resol query items = do
  let queries = possibleResolutions resol query
  Streamly.toList
    $ Streamly.parConcatMap
      id
      ( \item ->
          case streamToMaybe $ foldMapA (\query -> typeSearchOne tenv query item) queries of
            Nothing -> Streamly.nil
            Just res -> Streamly.cons res Streamly.nil
      )
    $ Streamly.fromList items

typeSearchOne :: TopEnv -> Term -> DbItem -> Stream TypeSearchResult
typeSearchOne tenv query DbItem {sig, original_sig_text, name_qual = name} = do
  (i, inst) <- check name (initCtx tenv, Here) (eval emptyMetaCtx tenv [] query) (eval emptyMetaCtx tenv [] sig)
  pure (TypeSearchResult name sig original_sig_text i inst)

displayTypeSearchResults :: [DbItem] -> [TypeSearchResult] -> NominalDiffTime -> InputT IO ()
displayTypeSearchResults cands matches time = do
  outputStrLn $ shows (length matches) $ showString " item(s) matched in " $ shows (length cands) " candidate(s)"
  outputStrLn $ showString "Took " $ shows time "\n"
  for_ matches \(TypeSearchResult (QName m x) _ origA i sol) -> do
    outputStrLn
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

--------------------------------------------------------------------------------
-- Search by name

displaySearchByNameResult :: [(QName, Term)] -> InputT IO ()
displaySearchByNameResult = traverse_ \(QName m x, a) -> do
  outputStrLn $ shows x $ showString " : " $ prettyTerm0 Unqualify a ""
  outputStrLn $ showString "  in " $ shows m "\n"
