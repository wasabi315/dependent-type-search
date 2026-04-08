module TypeSearch.MainInteraction (mainLoop) where

import Control.Applicative
import Control.Exception (displayException)
import Control.Monad
import Control.Monad.IO.Class
import Data.Foldable
import Data.Map.Strict qualified as M
import Data.Maybe
import Data.Set qualified as S
import Data.Text qualified as T
import Data.Time.Clock
import Database.PostgreSQL.Simple
import Stream
import Streamly.Data.Stream.Prelude qualified as Streamly
import System.Console.Haskeline
import TypeSearch.Common
import TypeSearch.Database.PostgreSQL
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

mainLoop :: Connection -> S.Set QName -> IO ()
mainLoop conn aliasSet = runInputT defaultSettings go
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
            cands <- liftIO $ filterByFeatures conn aliasSet typ
            case cands of
              Nothing -> outputStrLn "Ill-formed type" >> go
              Just cands -> do
                -- outputStrLn $ show $ map (.name_unqual) cands
                resol1 <- liftIO $ fetchResolution conn typ
                (tenv, resol2) <- liftIO $ fetchTopEnv conn $ map (.name_qual) cands
                (result, time) <- liftIO $ timed $ typeSearch tenv (M.unionWith (++) resol1 resol2) typ cands
                displayTypeSearchResults cands result time
                go

timed :: IO a -> IO (a, NominalDiffTime)
timed a = do
  t1 <- getCurrentTime
  res <- a
  t2 <- getCurrentTime
  let diff = diffUTCTime t2 t1
  pure (res, diff)

data TypeSearchResult = TypeSearchResult QName Term Iso Term

typeSearch :: TopEnv -> M.Map Name [QName] -> Raw -> [DbItem] -> IO [TypeSearchResult]
typeSearch tenv resol query items = do
  let queries = possibleResolutions resol query
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
typeSearchOne tenv query DbItem {sig = sig, name_qual = name} = do
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
      guard $ allMetaSolved mctx
      let j = i <> sym i'
          ~sol = closeTm locs $ quote mctx ctx.level $ transportInv j inst
      pure (j, sol)
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

displayTypeSearchResults :: [DbItem] -> [TypeSearchResult] -> NominalDiffTime -> InputT IO ()
displayTypeSearchResults cands matches time = do
  outputStrLn $ shows (length matches) $ showString " item(s) matched in " $ shows (length cands) " candidate(s)"
  outputStrLn $ showString "Took " $ shows time "\n"
  for_ matches \(TypeSearchResult (QName m x) a i sol) -> do
    outputStrLn $
      unlines $
        concat
          [ [ showString "- " $ shows x $ showString " : " $ prettyTerm0 Unqualify a "",
              showString "  - module       : " $ shows m ""
            ],
            case i of
              Refl -> []
              i -> [showString "  - isomorphism  : " $ prettyIso 0 i ""],
            [ showString "  - solution     : " $ prettyTerm0 Unqualify sol ""
            ]
          ]

--------------------------------------------------------------------------------
-- Search by name

displaySearchByNameResult :: [(QName, Term)] -> InputT IO ()
displaySearchByNameResult = traverse_ \(QName m x, a) -> do
  outputStrLn $ shows x $ showString " : " $ prettyTerm0 Unqualify a ""
  outputStrLn $ showString "  in " $ shows m "\n"
