module Aegle.Cli.Serve
  ( serve,
    Command (..),
  )
where

import Aegle.Database.Backend.PostgreSQL
import Aegle.Prelude
import Aegle.Web
import Control.Exception
import Hasql.Pool qualified as Pool
import Hasql.Pool.Config qualified as Pool
import Network.Wai.Handler.Warp qualified as Warp

--------------------------------------------------------------------------------

data Command = Command
  { poolConfig :: Pool.Config,
    port :: Warp.Port,
    timeout :: Int,
    agdaHtmlDir :: FilePath
  }

--------------------------------------------------------------------------------

serve :: Command -> IO ()
serve Command {..} =
  bracket (Pool.acquire poolConfig) Pool.release \pool -> do
    let dbReader = newDbReader pool
    runServer Config {..}
