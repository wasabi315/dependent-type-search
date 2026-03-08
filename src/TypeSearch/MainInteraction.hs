module TypeSearch.MainInteraction (mainLoop) where

import Control.Monad.IO.Class
import Data.Foldable
import Database.PostgreSQL.Simple
import System.Console.Haskeline
import TypeSearch.Common
import TypeSearch.Database.Common
import TypeSearch.Pretty

--------------------------------------------------------------------------------

data Command
  = Continue
  | Help
  | Quit
  | SearchByName String

parseCommand :: Maybe String -> Either String Command
parseCommand = maybe (pure Continue) \input -> case words input of
  [] -> pure Continue
  ":help" : _ -> pure Help
  ":h" : _ -> pure Help
  ":quit" : _ -> pure Quit
  ":q" : _ -> pure Quit
  (':' : cmd) : _ -> Left $ "Unknown command: " <> cmd
  "name" : name : _ -> pure $ SearchByName name
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
          fuzzySearchByName conn name
          go

--------------------------------------------------------------------------------
-- Search by name

fuzzySearchByName :: Connection -> String -> InputT IO ()
fuzzySearchByName conn name = do
  items :: [Only DbQName :. Only DbTerm :. Only Float] <-
    liftIO $ query conn "SELECT name_qual, sig, similarity(?, name_unqual) AS sml FROM library_items WHERE similarity(?, name_unqual) > 0.9 ORDER BY sml DESC" (name, name)
  for_ items \(Only (DbQName (QName m x)) :. Only (DbTerm a) :. _) -> do
    outputStrLn $ shows x $ showString " : " $ prettyTerm0 Unqualify a ""
    outputStrLn $ showString "  in " $ shows m "\n"
