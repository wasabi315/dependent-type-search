module TypeSearch.Database.Search
  ( search,
  )
where

import Data.ImmatureStream qualified as ImS
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import Data.Time.Clock
import Database.PostgreSQL.Simple
import Streamly.Data.Stream.Prelude qualified as Streamly
import System.Console.Haskeline
import TypeSearch.Core.Evaluation
import TypeSearch.Core.Isomorphism
import TypeSearch.Core.Name
import TypeSearch.Core.Term
import TypeSearch.Database.PostgreSQL
import TypeSearch.Database.Search.Parser
import TypeSearch.Database.Search.Query qualified as Q
import TypeSearch.Prelude
import TypeSearch.Pretty
import TypeSearch.Unification

--------------------------------------------------------------------------------

data Command
  = Continue
  | Help
  | Quit
  | Search String

parseCommand :: Maybe String -> Either String Command
parseCommand = maybe (pure Continue) \input -> case words input of
  [] -> pure Continue
  ":help" : _ -> pure Help
  ":h" : _ -> pure Help
  ":quit" : _ -> pure Quit
  ":q" : _ -> pure Quit
  (':' : cmd) : _ -> Left $ "Unknown command: " <> cmd
  _ -> pure $ Search input

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

search :: Connection -> S.Set QName -> IO ()
search conn transparentDefSet = runInputT defaultSettings go
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
        Right (Search typ) -> case parseQuery "interactive" (T.pack typ) of
          Left err -> outputStrLn (displayException err) >> go
          Right typ -> do
            cands <- liftIO $ filterByFeatures conn transparentDefSet typ
            case cands of
              Nothing -> outputStrLn "Ill-formed type" >> go
              Just cands -> do
                resol1 <- liftIO $ fetchResolution conn typ
                (tenv, resol2) <- liftIO $ fetchTopEnv conn $ map (.name_qual) cands
                (result, time) <- liftIO $ timed $ typeSearch tenv (M.unionWith (++) resol1 resol2) typ cands
                let sorted = sortOn (\(TypeSearchResult _ _ _ _ sol) -> termSize sol) result
                displayTypeSearchResults cands sorted time
                go

data TypeSearchResult = TypeSearchResult QName Type T.Text Iso Term

typeSearch :: TopEnv -> M.Map Name [QName] -> Q.Type -> [DbItem] -> IO [TypeSearchResult]
typeSearch tenv resol query items = do
  let queries = Q.possibleResolutions resol query
  Streamly.toList
    $ Streamly.parConcatMap
      id
      ( \item ->
          case ImS.streamToMaybe $ foldMapA (\query -> typeSearchOne tenv query item) queries of
            Nothing -> Streamly.nil
            Just res -> Streamly.cons res Streamly.nil
      )
    $ Streamly.fromList items

typeSearchOne :: TopEnv -> Term -> DbItem -> ImS.Stream TypeSearchResult
typeSearchOne tenv query DbItem {sig, original_sig_text, name_qual = name} = do
  (i, inst) <- check name (initCtx tenv, Here) (eval emptyMetaCtx tenv [] query) (eval emptyMetaCtx tenv [] sig)
  pure (TypeSearchResult name sig original_sig_text i inst)

displayTypeSearchResults :: [DbItem] -> [TypeSearchResult] -> NominalDiffTime -> InputT IO ()
displayTypeSearchResults cands matches time = do
  outputStrLn $ shows (length matches) $ showString " item(s) matched in " $ shows (length cands) " candidate(s)"
  outputStrLn $ showString "Took " $ shows time "\n"
  for_ matches \(TypeSearchResult (QName m x) _ origA i sol) -> do
    outputStrLn $
      unlines $
        concat
          [ [ showString "- " $ shows x $ showString " : " $ T.unpack origA,
              showString "  - module        : " $ shows m ""
            ],
            case i of
              Refl -> []
              i -> [showString "  - isomorphism   : " $ prettyIso 0 i ""],
            [ showString "  - solution      : " $ prettyTerm0 Unqualify sol ""
            ]
          ]
