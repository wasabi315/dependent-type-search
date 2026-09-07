{-# LANGUAGE ApplicativeDo #-}

module Aegle.Cli (main) where

import Aegle.Cli.Index qualified as Index
import Aegle.Cli.Interactive qualified as Interactive
import Aegle.Cli.Search qualified as Search
import Aegle.Cli.Serve qualified as Serve
import Aegle.Prelude hiding (reader)
import Data.Text qualified as T
import Hasql.Connection.Setting
import Hasql.Connection.Setting.Connection qualified as ConnSetting
import Hasql.Connection.Setting.Connection.Param
import Hasql.Pool.Config qualified as Pool
import OptEnvConf hiding (Command)
import Paths_aegle_app

--------------------------------------------------------------------------------
-- Options

data Command
  = Index Index.Command
  | Search Search.Command
  | Interactive Interactive.Command
  | Serve Serve.Command

instance HasParser Command where
  settingsParser =
    commands
      [ index,
        search,
        interactive,
        serve
      ]
    where
      index = command "index" "Index Agda libraries" do
        connSetting <- connectionSetting
        configFile <- argSetting "CONFIG_FILE" "YAML file listing Agda libraries to index" str
        enableStatistics <- longSwitchSetting "statistics" "Collect statistics"
        pure $ Index Index.Command {..}

      search = command "search" "Search within indexed library" do
        connSetting <- connectionSetting
        query <- argSetting "QUERY" "Type expression to search for" str
        timeout <- longSetting "timeout" "TIMEOUT" "Search timeout in μs" auto 10000000
        pure $ Search Search.Command {..}

      interactive = command "interactive" "Interactive search shell" do
        connSetting <- connectionSetting
        pure $ Interactive Interactive.Command {..}

      serve = command "serve" "Run web server" do
        poolConfig <- poolConfig
        port <- envSetting "PORT" "HTTP port to listen on" auto
        timeout <- longSetting "timeout" "TIMEOUT" "Search timeout in μs" auto 1000000
        agdaHtmlDir <- longSetting "html-dir" "HTML_DIR" "Directory containing generated Agda HTML files" str "html"
        pure $ Serve Serve.Command {..}

      connectionSetting =
        asum
          [ envSetting "DATABASE_URL" "PostgreSQL connection URI" do
              connection . ConnSetting.string . T.pack <$> str,
            do
              host <- envSetting "DATABASE_HOST" "PostgreSQL host" do
                host . T.pack <$> str
              port <- envSetting "DATABASE_PORT" "PostgreSQL port" do
                port <$> auto
              user <- envSetting "DATABASE_USER" "PostgreSQL user" do
                user . T.pack <$> str
              password <- envSetting "DATABASE_PASSWORD" "PostgreSQL password" do
                password . T.pack <$> str
              database <- envSetting "DATABASE_NAME" "PostgreSQL database name" do
                dbname . T.pack <$> str
              pure $ connection $ ConnSetting.params [host, port, user, password, database]
          ]

      poolConfig = do
        connSetting <- connectionSetting
        pure $ Pool.settings [Pool.staticConnectionSettings [connSetting]]

      argSetting var helpText readf =
        setting [argument, reader readf, metavar var, help helpText]

      longSetting opt var helpText readf def =
        setting [option, long opt, reader readf, metavar var, help helpText, value def]

      envSetting var helpText readf =
        setting [env var, metavar var, reader readf, help helpText]

      longSwitchSetting opt helpText =
        setting [switch True, value False, long opt, help helpText]

--------------------------------------------------------------------------------

main :: IO ()
main = do
  cmd <- runSettingsParser version "Type-based library search for Agda"
  case cmd of
    Index cmd -> Index.index cmd
    Search cmd -> Search.search cmd
    Interactive cmd -> Interactive.interactive cmd
    Serve cmd -> Serve.serve cmd
