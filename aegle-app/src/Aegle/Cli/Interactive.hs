module Aegle.Cli.Interactive
  ( interactive,
    Command (..),
  )
where

import Aegle.Cli.Search qualified as Search
import Aegle.Database.Backend.PostgreSQL
import Aegle.Prelude
import Control.Exception
import Data.Generics.Labels ()
import Data.Text qualified as T
import Hasql.Connection
import Hasql.Connection.Setting
import System.Console.Repline hiding (Command)
import System.Exit

--------------------------------------------------------------------------------

newtype Command = Command
  { connSetting :: Setting
  }

--------------------------------------------------------------------------------

newtype ReplState = ReplState
  { timeout :: Int
  }
  deriving stock (Generic)

initReplState :: ReplState
initReplState =
  ReplState
    { timeout = 10000000
    }

-- Interactive search shell
interactive :: Command -> IO ()
interactive Command {..} =
  withConnect connSetting \conn -> do
    let dbReader = newDbReader conn
    flip evalStateT initReplState do
      evalReplOpts ReplOpts {command = command dbReader, ..}
  where
    banner _ = pure ">> "
    command dbReader cmd = do
      timeout <- gets (.timeout)
      liftIO $ Search.searchWith dbReader timeout $ T.pack cmd
    prefix = Just '!'
    multilineCommand = Nothing
    tabComplete = Word0 (listWordCompleter [])
    initialiser = liftIO $ putStrLn "Welcome to Aegle!"
    finaliser = liftIO $ Exit <$ putStrLn "Bye!"

    options = [("help", help), ("timeout", timeout)]
    help _ =
      liftIO
        $ putStrLn
          """
          Commands:
            !help          : show this help text
            !timeout <μs>  : set timeout (negative value for infinite)
            <type>         : search for definitions by type

          """
    timeout args = case words args of
      (readMaybe @Int -> Just ms) : _ -> #timeout .= ms
      _ -> liftIO $ putStrLn "Failed to parse timeout"

--------------------------------------------------------------------------------

orDie :: IO (Either String a) -> IO a
orDie m = m >>= either die pure

withConnect :: Setting -> (Connection -> IO r) -> IO r
withConnect connSetting =
  bracket (orDie $ first show <$> acquire [connSetting]) release
