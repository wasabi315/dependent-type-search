module Main (main) where

import Data.Maybe
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Migration
import Options.Applicative
import System.Environment (getEnv, lookupEnv)
import TypeSearch.Database.Index
import TypeSearch.MainInteraction

getConnectInfo :: IO ConnectInfo
getConnectInfo = do
  connectHost <- fromMaybe "127.0.0.1" <$> lookupEnv "DATABASE_HOST"
  connectPort <- maybe 5432 read <$> lookupEnv "DATABASE_PORT"
  connectUser <- getEnv "DATABASE_USER"
  connectPassword <- getEnv "DATABASE_PASSWORD"
  connectDatabase <- getEnv "DATABASE_NAME"
  pure $! ConnectInfo {..}

data TopCommand
  = Index FilePath
  | Search

opts :: Parser TopCommand
opts =
  hsubparser
    ( command "index" (info (Index <$> argument str (metavar "PATH_TO_LIBRARY")) (progDesc "Index an Agda library"))
        <> command "search" (info (pure Main.Search) (progDesc "Search within indexed library"))
    )

main :: IO ()
main = do
  command <- execParser (info opts idm)
  connInfo <- getConnectInfo
  case command of
    Index libDir -> do
      withConnect connInfo \conn -> do
        _ <-
          runMigrations
            conn
            defaultOptions
            [MigrationInitialization, MigrationDirectory "migration"]
        translateLibrary (IndexConfig 80 libDir conn)
    Main.Search -> withConnect connInfo mainLoop
