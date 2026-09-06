module Aegle.Cli.Search
  ( Aegle.Cli.Search.search,
    searchWith,
    Command (..),
  )
where

import Aegle.Core.Isomorphism
import Aegle.Core.Name
import Aegle.Core.Term
import Aegle.Database.Backend
import Aegle.Database.Backend.PostgreSQL
import Aegle.Prelude
import Aegle.Search as Search
import Control.Exception
import Data.Text qualified as T
import Hasql.Connection
import Hasql.Connection.Setting
import Prettyprinter
import Prettyprinter.Render.Terminal
import Prettyprinter.Render.Text
import Prettyprinter.Util
import System.Directory
import System.Exit
import System.FilePath
import System.IO

--------------------------------------------------------------------------------

data Command = Command
  { connSetting :: Setting,
    timeout :: Int,
    query :: T.Text
  }

--------------------------------------------------------------------------------

search :: Command -> IO ()
search Command {..} =
  withConnect connSetting \conn -> do
    let dbReader = newDbReader conn
    searchWith dbReader timeout query

searchWith :: DbReader IO -> Int -> T.Text -> IO ()
searchWith dbReader timeout query = do
  let config =
        Search.Config
          { querySrc = "<interactive>",
            recordCandTimes = True,
            ..
          }
  result <- Search.search config query
  for_ (result ^? _Right . #candTimes . _Just) $ writeCandTimes query
  either putError putResult result

putResult :: Result -> IO ()
putResult Result {..} =
  Prettyprinter.Render.Terminal.putDoc (doc <> line)
  where
    numMatches = length matches

    doc =
      vsep
        [ numDoc,
          timeDoc,
          case matches of
            [] -> emptyDoc
            _ -> enclose line line matchesDoc
        ]

    numDoc =
      hsep
        [ pretty numMatches,
          plural "item" "items" numMatches,
          reflow "matched in",
          pretty numCands,
          plural "candidate" "candidates" numCands
        ]

    timeDoc = "Took" <+> viaShow time

    matchesDoc =
      concatWith (surround $ line <> line) do
        -- rank by solution size
        matchDoc <$> sortOn (termSize . (.solution)) matches

    matchDoc Match {item = LibraryItem {..}, ..} =
      vsep
        [ annotate (bold <> color Green) do
            "∙" <+> pretty (ignoreLibName canonicalName) <+> colon <+> pretty (Unqualified originalSignature),
          indent 2
            $ vsep
            $ catMaybes
              [ Just $ "◦ library        :" <+> pretty canonicalName.libName,
                Just $ "◦ kind           :" <+> kindDoc kind,
                case reexportedAs of
                  [] -> Nothing
                  _ -> Just $ "◦ re-exported as :" <+> hsep (punctuate comma $ reexportedAs <&> \name -> pretty name.libName <+> pretty (ignoreLibName name)),
                case iso of
                  Refl -> Nothing
                  _ -> Just $ "◦ isomorphism    :" <+> pretty iso,
                case solution of
                  Opaque {} -> Nothing
                  _ -> Just $ "◦ solution       :" <+> pretty (Unqualified solution)
              ]
        ]

    kindDoc = \case
      DKPostulate -> "postulate"
      DKFunction -> "function"
      DKDatatype -> "data"
      DKRecord -> "record"
      DKConstructor -> "constructor"
      DKPrimitive -> "primitive"

writeCandTimes :: T.Text -> [CandTime] -> IO ()
writeCandTimes query candTimes = do
  cwd <- getCurrentDirectory
  let logDir = cwd </> ".aegle-log" </> "search"
      logFile = logDir </> "candidate-times.log"
  createDirectoryIfMissing True logDir
  let doc =
        vsep
          [ "--------------------------------------------------------------------------------",
            "query:" <+> pretty query,
            "candidate timings, slowest first:",
            indent 2 $ vsep $ candTimeDoc <$> sortOn (Down . (.time)) candTimes
          ]
  withFile logFile AppendMode \hdl ->
    Prettyprinter.Render.Text.hPutDoc hdl (doc <> line)
  where
    candTimeDoc CandTime {name, time, matched} =
      hsep
        [ viaShow time,
          if matched then "matched" else "missed",
          pretty name
        ]

putError :: Error -> IO ()
putError = hPutStrLn stderr . displayException

--------------------------------------------------------------------------------

orDie :: IO (Either String a) -> IO a
orDie m = m >>= either die pure

withConnect :: Setting -> (Connection -> IO r) -> IO r
withConnect connSetting =
  bracket (orDie $ first show <$> acquire [connSetting]) release
