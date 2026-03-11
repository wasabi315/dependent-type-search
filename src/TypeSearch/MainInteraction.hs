module TypeSearch.MainInteraction (mainLoop) where

import Control.Exception (displayException)
import Control.Monad.IO.Class
import Data.Foldable
import Data.HashMap.Lazy qualified as HML
import Data.List (isPrefixOf)
import Data.Map.Strict qualified as M
import Data.Maybe
import Data.Set qualified as S
import Data.Text qualified as T
import Database.PostgreSQL.Simple
import Debug.Trace
import System.Console.Haskeline
import TypeSearch.Common
import TypeSearch.Database.Common
import TypeSearch.Evaluation
import TypeSearch.Parser
import TypeSearch.Pretty
import TypeSearch.Raw
import TypeSearch.Term
import TypeSearch.UnificationModuloIso

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

mainLoop :: Connection -> IO ()
mainLoop conn = runInputT defaultSettings go
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
            -- liftIO $ putStrLn $ prettyRaw 0 typ ""
            (bcs, resol1) <- liftIO $ fetchBodyCanonish conn typ
            -- liftIO $ print bcs
            rsbm <- liftIO $ fetchReturnSortBody conn typ
            -- liftIO $ print rsbm
            cands <- liftIO $ filterByFeatures conn bcs rsbm typ
            -- cands <- liftIO $ Just <$> fetchAllItems conn
            case cands of
              Nothing -> outputStrLn "Ill-formed type" >> go
              Just cands -> do
                -- outputStrLn $ "Number of candidates: " ++ show (length cands)
                (tenv, resol2) <- liftIO $ fetchTopEnv conn $ map (\item -> item.name_qual) cands
                -- outputStrLn $ "Size of top env: " ++ show (HML.size topEnv)
                displayTypeSearchResult $ typeSearch tenv (M.unionWith (++) resol1 resol2) typ cands
                go

data TypeSearchResult = TypeSearchResult QName Term Iso

typeSearch :: TopEnv -> M.Map Name [QName] -> Raw -> [DbItem] -> [TypeSearchResult]
typeSearch tenv resol query items = do
  let queries = possibleResolutions resol query
  -- queries' = trace (unlines $ map (\q -> prettyTerm0 Qualify q "") queries) queries
  mapMaybe (\item -> foldMapA (\query -> typeSearchOne tenv query item) queries) items

typeSearchOne :: TopEnv -> Term -> DbItem -> Maybe TypeSearchResult
typeSearchOne tenv query DbItem {sig = DbTerm sig, name_qual = DbQName name} = do
  (i, _) <- listToMaybe $ unifyIso0 emptyMetaCtx tenv query sig
  pure (TypeSearchResult name sig i)

displayTypeSearchResult :: [TypeSearchResult] -> InputT IO ()
displayTypeSearchResult = traverse_ \(TypeSearchResult (QName m x) a i) -> do
  outputStrLn $ shows x $ showString " : " $ prettyTerm0 Unqualify a ""
  outputStrLn $ showString "  in " $ shows m ""
  outputStrLn $ showString "  iso : " $ prettyIso 0 i "\n"

--------------------------------------------------------------------------------
-- Search by name

displaySearchByNameResult :: [(DbQName, DbTerm)] -> InputT IO ()
displaySearchByNameResult = traverse_ \(DbQName (QName m x), DbTerm a) -> do
  outputStrLn $ shows x $ showString " : " $ prettyTerm0 Unqualify a ""
  outputStrLn $ showString "  in " $ shows m "\n"
