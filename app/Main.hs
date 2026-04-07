module Main (main) where

import Data.Aeson (eitherDecodeFileStrict)
import Data.Maybe
import Data.Set qualified as S
import Data.Text qualified as T
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Migration
import Options.Applicative
import Paths_dependent_type_search
import System.Environment (getEnv, lookupEnv)
import System.Exit
import System.FilePath
import System.IO
import TypeSearch.Common hiding (Index)
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
  | Search FilePath

opts :: Parser TopCommand
opts =
  hsubparser
    ( command "index" (info (Index <$> argument str (metavar "PATH_TO_LIBRARY") <*> argument str (metavar "PATH_TO_ALIASE_FILE")) (progDesc "Index an Agda library"))
        <> command "search" (info (Main.Search <$> argument str (metavar "PATH_TO_ALIASE_FILE")) (progDesc "Search within indexed library"))
    )

main :: IO ()
main = do
  command <- execParser (info opts idm)
  connInfo <- getConnectInfo
  case command of
    Index libDir aliasFile -> do
      alias <-
        eitherDecodeFileStrict aliasFile >>= \case
          Right transp -> pure transp
          Left err -> hPutStrLn stderr err >> exitFailure
      withConnect connInfo \conn -> do
        dataDir <- getDataDir
        let migrationDir = dataDir </> "migration"
        _ <-
          runMigrations
            conn
            defaultOptions
            [MigrationInitialization, MigrationDirectory migrationDir]
        translateLibrary (IndexConfig alias libDir conn)
    Main.Search aliasFile -> do
      alias <-
        eitherDecodeFileStrict aliasFile >>= \case
          Right transp -> pure transp
          Left err -> hPutStrLn stderr err >> exitFailure
      let alias' = flip S.map alias \x -> do
            let xs = T.splitOn "." x
                m = coerce $ T.intercalate "." (init xs)
                f = coerce $ last xs
            QName m f
      withConnect connInfo (flip mainLoop alias')
