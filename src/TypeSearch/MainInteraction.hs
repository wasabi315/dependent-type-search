module TypeSearch.MainInteraction (mainLoop) where

import Control.Exception (displayException)
import Control.Monad.IO.Class
import Data.Foldable
import Data.HashMap.Lazy qualified as HML
import Data.Text qualified as T
import Database.PostgreSQL.Simple
import System.Console.Haskeline
import TypeSearch.Common
import TypeSearch.Database.Common
import TypeSearch.Evaluation
import TypeSearch.Parser
import TypeSearch.Pretty
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
            bcs <- liftIO $ fetchBodyCanonish conn typ
            -- liftIO $ print bcs
            rsbm <- liftIO $ fetchReturnSortBody conn typ
            -- liftIO $ print rsbm
            cands <- liftIO $ filterByFeatures conn bcs rsbm typ
            case cands of
              Nothing -> outputStrLn "Ill-formed type" >> go
              Just cands -> do
                -- outputStrLn $ "Number of candidates: " ++ show (length cands)
                _topEnv <- liftIO $ fetchTopEnv conn $ map (\item -> item.name_qual) cands
                -- outputStrLn $ "Size of top env: " ++ show (HML.size topEnv)
                go

-- typeSearch :: R

--------------------------------------------------------------------------------
-- Search by name

displaySearchByNameResult :: [(DbQName, DbTerm)] -> InputT IO ()
displaySearchByNameResult = traverse_ \(DbQName (QName m x), DbTerm a) -> do
  outputStrLn $ shows x $ showString " : " $ prettyTerm0 Unqualify a ""
  outputStrLn $ showString "  in " $ shows m "\n"
