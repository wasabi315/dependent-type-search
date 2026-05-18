module TypeSearch.Cli (main) where

import Data.Aeson (eitherDecodeFileStrict)
import Data.Maybe
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Migration
import Options.Applicative
import Paths_dependent_type_search
import System.Environment (getEnv, lookupEnv)
import System.Exit
import System.FilePath
import System.IO
import TypeSearch.Database.Index qualified as Index
import TypeSearch.Prelude
import TypeSearch.Search qualified as Search

--------------------------------------------------------------------------------
-- Options

getConnectInfo :: IO ConnectInfo
getConnectInfo = do
  connectHost <- fromMaybe "127.0.0.1" <$> lookupEnv "DATABASE_HOST"
  connectPort <- maybe 5432 read <$> lookupEnv "DATABASE_PORT"
  connectUser <- getEnv "DATABASE_USER"
  connectPassword <- getEnv "DATABASE_PASSWORD"
  connectDatabase <- getEnv "DATABASE_NAME"
  pure $! ConnectInfo {..}

data Command
  = Index IndexCommand
  | Search SearchCommand

data IndexCommand = IndexCommand
  { libraryDir :: FilePath,
    transparentDefsFile :: FilePath
  }

newtype SearchCommand = SearchCommand
  { transparentDefsFile :: FilePath
  }

optIndexCommand :: Parser IndexCommand
optIndexCommand =
  IndexCommand
    <$> argument str (metavar "LIBRARY_DIR")
    <*> argument str (metavar "TRANSPARENT_DEFS_FILE")

optSearchCommand :: Parser SearchCommand
optSearchCommand =
  SearchCommand
    <$> argument str (metavar "TRANSPARENT_DEFS_FILE")

opts :: Parser Command
opts =
  hsubparser $
    mconcat
      [ command "index" (info (Index <$> optIndexCommand) (progDesc "Index an Agda library")),
        command "search" (info (Search <$> optSearchCommand) (progDesc "Search within indexed library"))
      ]

--------------------------------------------------------------------------------

dispatchCommand :: Command -> ConnectInfo -> IO ()
dispatchCommand = \cases
  (Index cmd) connInfo -> index cmd connInfo
  (Search cmd) connInfo -> search cmd connInfo

index :: IndexCommand -> ConnectInfo -> IO ()
index (IndexCommand {..}) connInfo = do
  transparentDef <-
    eitherDecodeFileStrict transparentDefsFile >>= \case
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
    Index.indexLibrary (Index.IndexConfig transparentDef libraryDir conn)

search :: SearchCommand -> ConnectInfo -> IO ()
search (SearchCommand {..}) connInfo = do
  transparentDef <-
    eitherDecodeFileStrict transparentDefsFile >>= \case
      Right transp -> pure transp
      Left err -> hPutStrLn stderr err >> exitFailure
  withConnect connInfo (flip Search.search transparentDef)

main :: IO ()
main = do
  command <- execParser (info opts fullDesc)
  connInfo <- getConnectInfo
  dispatchCommand command connInfo
