module TypeSearch.MainInteraction (mainLoop) where

import Control.Applicative
import Control.Exception (displayException)
import Control.Monad.IO.Class
import Data.Foldable
import Data.HashMap.Lazy qualified as HML
import Data.HashMap.Strict qualified as HM
import Data.List (isPrefixOf)
import Data.Map.Strict qualified as M
import Data.Maybe
import Data.Set qualified as S
import Data.Text qualified as T
import Database.PostgreSQL.Simple
import Debug.Trace
import Stream
import Streamly.Data.Stream.Prelude qualified as Streamly
import System.Console.Haskeline
import TypeSearch.Common
import TypeSearch.Database.Common
import TypeSearch.Evaluation
import TypeSearch.Parser
import TypeSearch.Pretty
import TypeSearch.Raw
import TypeSearch.Term
import TypeSearch.Unification
import TypeSearch.UnificationModuloIso

--------------------------------------------------------------------------------

data Command
  = Continue
  | Help
  | Quit
  | SearchByName String
  | SearchByType String

parseCommand :: Maybe String -> Either String Command
parseCommand = maybe (pure Continue) \input -> case words input of
  [] -> pure Continue
  ":help" : _ -> pure Help
  ":h" : _ -> pure Help
  ":quit" : _ -> pure Quit
  ":q" : _ -> pure Quit
  (':' : cmd) : _ -> Left $ "Unknown command: " <> cmd
  "name" : name : _ -> pure $ SearchByName name
  "type" : rest -> pure $ SearchByType (unwords rest)
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
          items <- liftIO $ fuzzySearchByName conn name
          displaySearchByNameResult items
          go
        Right (SearchByType typ) -> case parseRaw "interactive" (T.pack typ) of
          Left err -> outputStrLn (displayException err) >> go
          Right typ -> do
            -- liftIO $ putStrLn $ prettyRaw 0 typ ""
            (bcs, resol1) <- liftIO $ fetchBodyCanonish conn typ
            -- liftIO $ print bcs
            rsbm <- liftIO $ fetchReturnSortBody conn typ
            -- liftIO $ print rsbm
            cands <- liftIO $ filterByFeatures conn bcs rsbm typ
            -- cands <- liftIO $ Just <$> fetchAllItems conn
            case cands of
              Nothing -> outputStrLn "Ill-formed type" >> go
              Just cands -> do
                -- outputStrLn $ "Number of candidates: " ++ show (length cands)
                (tenv, resol2) <- liftIO $ fetchTopEnv conn $ map (\item -> item.name_qual) cands
                -- outputStrLn $ "Size of top env: " ++ show (HML.size topEnv)
                result <- liftIO $ typeSearch tenv (M.unionWith (++) resol1 resol2) typ cands
                displayTypeSearchResult result
                go

data TypeSearchResult = TypeSearchResult QName Term Iso Term

typeSearch :: TopEnv -> M.Map Name [QName] -> Raw -> [DbItem] -> IO [TypeSearchResult]
typeSearch tenv resol query items = do
  let queries = possibleResolutions resol query
  -- queries' = trace (unlines $ map (\q -> prettyTerm0 Qualify q "") queries) queries
  Streamly.toList
    $ Streamly.parConcatMap
      id
      ( \item ->
          case streamToMaybe $ foldMapA (\query -> typeSearchOne tenv query item) queries of
            Nothing -> Streamly.nil
            Just res -> Streamly.cons res Streamly.nil
      )
    $ Streamly.fromList items

typeSearchOne :: TopEnv -> Term -> DbItem -> Stream TypeSearchResult
typeSearchOne tenv query DbItem {sig = DbTerm sig, name_qual = DbQName name} = do
  (i, inst) <- check name (initCtx tenv, Here) (eval emptyMetaCtx tenv [] query) (eval emptyMetaCtx tenv [] sig)
  pure (TypeSearchResult name sig i inst)

data Locals
  = Here
  | Bind Locals Name ~Term

closeTy :: Locals -> Term -> Term
closeTy = \cases
  Here b -> b
  (Bind locs x a) b -> closeTy locs (Pi x a b)

closeTm :: Locals -> Term -> Term
closeTm = \cases
  Here t -> t
  (Bind locs x _) b -> closeTm locs (Lam x b)

check :: QName -> (Ctx, Locals) -> Value -> Value -> Stream (Iso, Term)
check h (ctx, locs) query item =
  ( do
      (item, inst, mctx) <- possibleInstantiation emptyMetaCtx (ctx, locs) item (VTop h SNil Nothing)
      (i, i', mctx) <- maybeToStream $ listToMaybe $ unifyIso mctx ctx query item
      let j = i <> sym i'
          ~inst' = closeTm locs $ quote mctx ctx.level $ transport j inst
      pure (j, inst')
  )
    <|> Later case forceAll emptyMetaCtx query of
      VPi "_" _ _ -> empty
      VPi x a b -> do
        check h (bind ctx, Bind locs x (quote emptyMetaCtx ctx.level a)) (b $ VVar ctx.level) item
      _ -> empty

freshMeta :: MetaCtx -> Ctx -> Locals -> Value -> (Term, MetaCtx)
freshMeta mctx ctx locs a = do
  let ~closed = eval mctx ctx.topEnv [] $ closeTy locs (quote mctx ctx.level a)
      (m, mctx') = newMeta mctx closed
  (AppPruning (Meta m) (replicate (coerce ctx.level) True), mctx')

possibleInstantiation :: MetaCtx -> (Ctx, Locals) -> Value -> Value -> Stream (Value, Value, MetaCtx)
possibleInstantiation mctx (ctx, locs) a ~inst =
  pure (a, inst, mctx)
    <|> Later case forceAll mctx a of
      VPi "_" _ _ -> empty
      VPi _ a b -> do
        (m, mctx) <- pure $ freshMeta mctx ctx locs a
        let mv = eval mctx ctx.topEnv ctx.env m
        possibleInstantiation mctx (ctx, locs) (b mv) (inst $$ mv)
      _ -> empty

displayTypeSearchResult :: [TypeSearchResult] -> InputT IO ()
displayTypeSearchResult = traverse_ \(TypeSearchResult (QName m x) a i inst) -> do
  outputStrLn $
    unlines $
      concat
        [ [ showString "- " $ shows x $ showString " : " $ prettyTerm0 Unqualify a "",
            showString "  - module        : " $ shows m ""
          ],
          case i of
            Refl -> []
            i -> [showString "  - isomorphism   : " $ prettyIso 0 i ""],
          [ showString "  - instantiation : " $ prettyTerm0 Unqualify inst ""
          ]
        ]

--------------------------------------------------------------------------------
-- Search by name

displaySearchByNameResult :: [(DbQName, DbTerm)] -> InputT IO ()
displaySearchByNameResult = traverse_ \(DbQName (QName m x), DbTerm a) -> do
  outputStrLn $ shows x $ showString " : " $ prettyTerm0 Unqualify a ""
  outputStrLn $ showString "  in " $ shows m "\n"
