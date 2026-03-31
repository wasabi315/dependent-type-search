module Main (main) where

import Data.Aeson (eitherDecodeFileStrict)
import Data.Maybe
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Migration
import Options.Applicative
import System.Environment (getEnv, lookupEnv)
import System.Exit
import System.IO
import TypeSearch.Database.Index
import TypeSearch.Database.Index.Common
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
  = Index FilePath FilePath
  | Search

opts :: Parser TopCommand
opts =
  hsubparser
    ( command "index" (info (Index <$> argument str (metavar "PATH_TO_LIBRARY") <*> argument str (metavar "PATH")) (progDesc "Index an Agda library"))
        <> command "search" (info (pure Main.Search) (progDesc "Search within indexed library"))
    )

main :: IO ()
main = do
  command <- execParser (info opts idm)
  connInfo <- getConnectInfo
  case command of
    Index libDir transpFile -> do
      transp <-
        eitherDecodeFileStrict transpFile >>= \case
          Right transp -> pure transp
          Left err -> hPutStrLn stderr err >> exitFailure
      withConnect connInfo \conn -> do
        _ <-
          runMigrations
            conn
            defaultOptions
            [MigrationInitialization, MigrationDirectory "migration"]
        translateLibrary (IndexConfig transp libDir conn)
    Main.Search -> withConnect connInfo mainLoop
