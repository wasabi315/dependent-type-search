module TypeSearch.Cli (main) where

import Data.Aeson (eitherDecodeFileStrict)
import Data.Maybe
import Data.Text qualified as T
import Database.PostgreSQL.Simple
import Options.Applicative
import System.Environment (getEnv, lookupEnv)
import System.Exit
import System.FilePath
import TypeSearch.Database.Index qualified as Index
import TypeSearch.Database.Search qualified as Search
import TypeSearch.Prelude

--------------------------------------------------------------------------------
-- Options

getConnectInfo :: IO ConnectInfo
getConnectInfo = do
  connectHost <- fromMaybe "127.0.0.1" <$> lookupEnv "DATABASE_HOST"
  connectPort <- maybe 5432 read <$> lookupEnv "DATABASE_PORT"
  connectUser <- getEnv "DATABASE_USER"
  connectPassword <- getEnv "DATABASE_PASSWORD"
  connectDatabase <- getEnv "DATABASE_NAME"
  pure ConnectInfo {..}

data Command
  = Index IndexCommand
  | Search SearchCommand
  | InteractiveSearch InteractiveSearchCommand

data IndexCommand = IndexCommand
  { libraryDir :: FilePath,
    transparentDefsFile :: FilePath
  }

data SearchCommand = SearchCommand
  { transparentDefsFile :: FilePath,
    query :: T.Text
  }

newtype InteractiveSearchCommand = InteractiveSearchCommand
  { transparentDefsFile :: FilePath
  }

optIndexCommand :: Parser IndexCommand
optIndexCommand =
  IndexCommand
    <$> strArgument (metavar "LIBRARY_DIR")
    <*> strArgument (metavar "TRANSPARENT_DEFS_FILE")

optSearchCommand :: Parser SearchCommand
optSearchCommand =
  SearchCommand
    <$> strArgument (metavar "TRANSPARENT_DEFS_FILE")
    <*> strArgument (metavar "QUERY")

optInteractiveSearchCommand :: Parser InteractiveSearchCommand
optInteractiveSearchCommand =
  InteractiveSearchCommand
    <$> strArgument (metavar "TRANSPARENT_DEFS_FILE")

commandDesc :: String -> String -> Parser a -> Mod CommandFields a
commandDesc cmd desc p = command cmd $ info p (progDesc desc)

optCommand :: Parser Command
optCommand =
  hsubparser
    $ mconcat
      [ commandDesc "index" "Index an Agda Library" do
          Index <$> optIndexCommand,
        commandDesc "search" "Search within indexed library" do
          Search <$> optSearchCommand,
        commandDesc "interactive" "Interactive search shell" do
          InteractiveSearch <$> optInteractiveSearchCommand
      ]

main :: IO ()
main = do
  command <- execParser (info (optCommand <**> helper) fullDesc)
  connInfo <- getConnectInfo
  dispatchCommand command connInfo

--------------------------------------------------------------------------------

orDie :: IO (Either String a) -> IO a
orDie m = m >>= either die pure

dispatchCommand :: Command -> ConnectInfo -> IO ()
dispatchCommand = \case
  Index cmd -> index cmd
  Search cmd -> search cmd
  InteractiveSearch cmd -> interactive cmd

index :: IndexCommand -> ConnectInfo -> IO ()
index IndexCommand {..} connInfo = do
  transparentDefNames <- orDie $ eitherDecodeFileStrict transparentDefsFile
  withConnect connInfo \dbConn -> do
    Index.indexLibrary Index.Config {..}

search :: SearchCommand -> ConnectInfo -> IO ()
search SearchCommand {..} connInfo = do
  transparentDefNames <- orDie $ eitherDecodeFileStrict transparentDefsFile
  withConnect connInfo \conn -> do
    Search.search conn transparentDefNames query

interactive :: InteractiveSearchCommand -> ConnectInfo -> IO ()
interactive InteractiveSearchCommand {..} connInfo = do
  transparentDefNames <- orDie $ eitherDecodeFileStrict transparentDefsFile
  withConnect connInfo \conn -> do
    Search.interactive conn transparentDefNames
