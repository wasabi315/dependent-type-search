module Main (main) where

-- import Control.Exception
-- import Control.Monad
-- import Control.Monad.Except
-- import Data.Foldable
-- import Data.HashMap.Lazy qualified as HM
-- import Data.Text qualified as T
-- import Data.Text.IO qualified as T
-- import Data.Traversable
-- import Numeric.Natural
-- import System.Console.Haskeline
-- import System.Directory
-- import System.Environment
-- import System.Exit (exitFailure)
-- import System.FilePath
-- import System.IO
-- import System.Timeout
-- import Text.Read (readMaybe)
-- import TypeSearch.Common
-- import TypeSearch.Evaluation
-- import TypeSearch.Parser
-- import TypeSearch.Pretty
-- import TypeSearch.Raw
-- import TypeSearch.Term
-- import TypeSearch.UnificationModulo
-- import Witherable

-- data Generalise = Generalise | NoGeneralise
--   deriving stock (Eq)

-- data Options = Options
--   { generalise :: Generalise,
--     modulo :: Modulo,
--     timeoutMs :: Int
--   }

-- data Command
--   = Continue
--   | Help
--   | Quit
--   | SetOption (Options -> Options)
--   | Search Raw

-- parseCommand :: Maybe String -> Either String Command
-- parseCommand = maybe (pure Continue) \input -> case words input of
--   ":help" : _ -> pure Help
--   ":h" : _ -> pure Help
--   ":quit" : _ -> pure Quit
--   ":q" : _ -> pure Quit
--   ":set" : rest -> SetOption <$> parseOption rest
--   (':' : cmd) : _ -> Left $ "Unknown command: " <> cmd
--   _ -> case parseRaw "interactive" (T.pack input) of
--     Left e -> Left $ displayException e
--     Right ty -> pure $ Search ty

-- parseOption :: [String] -> Either String (Options -> Options)
-- parseOption = \case
--   [] -> pure id
--   "generalise" : rest -> do
--     f <- parseOption rest
--     pure \o -> f o {generalise = Generalise}
--   "no-generalise" : rest -> do
--     f <- parseOption rest
--     pure \o -> f o {generalise = NoGeneralise}
--   "modulo-iso" : rest -> do
--     f <- parseOption rest
--     pure \o -> f o {modulo = Iso}
--   "no-modulo-iso" : rest -> do
--     f <- parseOption rest
--     pure \o -> f o {modulo = DefEq}
--   "timeout" : ms : rest -> case readMaybe @Natural ms of
--     Nothing -> Left $ "Invalid timeout: " <> ms
--     Just ms' -> do
--       f <- parseOption rest
--       pure \o -> f o {timeoutMs = fromIntegral ms'}
--   tok : _ -> Left $ "Unknown option: " <> tok

-- defaultOptions :: Options
-- defaultOptions =
--   Options
--     { generalise = Generalise,
--       modulo = Iso,
--       timeoutMs = 5
--     }

-- helpText :: String
-- helpText =
--   unlines
--     [ "TypeSearch",
--       "  Type-directed search for dependent types",
--       "",
--       "Commands:",
--       "  :help, :h      : show this help text",
--       "  :quit, :q      : quit the program",
--       "  :set <option>  : set an option",
--       "  <type>         : search for definitions whose type matches <type>",
--       "",
--       "Options:",
--       "  (no-)generalise  : enable/disable search up to generalisation             (default=enabled)",
--       "  (no-)modulo-iso  : enable/disable search modulo βη and type isomorphisms  (default=enabled)",
--       "  timeout <ms>     : set the timeout in milliseconds                        (default=5)"
--     ]

-- mainLoop :: TopEnv -> [(QName, Raw)] -> InputT IO ()
-- mainLoop topEnv sigs = go defaultOptions
--   where
--     go opts = do
--       input <- getInputLine "> "
--       case parseCommand input of
--         Left err -> do
--           outputStrLn err
--           go opts
--         Right Continue -> go opts
--         Right Help -> do
--           outputStrLn helpText
--           go opts
--         Right Quit -> outputStrLn "Bye!"
--         Right (SetOption f) -> go (f opts)
--         Right (Search ty) -> do
--           search topEnv sigs ty opts
--           go opts

-- displayResult :: QName -> Raw -> MetaSubst -> InputT IO ()
-- displayResult name sig subst = do
--   outputStrLn $ shows name $ showString " : " $ prettyRaw 0 sig ""
--   let inst = flip imapMaybe subst \k (MetaAbs _ body) -> case k of
--         Inst {} -> Just body
--         _ -> Nothing
--       subst' = flip ifilter subst \k _ -> case k of Src _ -> True; _ -> False
--   when (HM.size inst > 0) do
--     let ~(Inst _ ns : _) = HM.keys inst
--         inst' = HM.mapKeys (\ ~(Inst x _) -> x) inst
--     outputStrLn $ "  instantiation: " ++ prettyInst ns inst' ""
--   when (HM.size subst' > 0) do
--     outputStrLn $ "  substitution: " ++ prettyMetaSubst subst' ""

-- search :: TopEnv -> [(QName, Raw)] -> Raw -> Options -> InputT IO ()
-- search topEnv sigs ty opts = do
-- let unify = if opts.generalise == Generalise then unifyRawInst else unifyRaw
-- for_ sigs \(x, sig) -> do
--   -- outputStrLn $ shows x ""
--   msubst <-
--     liftIO $
--       timeout (opts.timeoutMs * 1000) do
--         unify opts.modulo topEnv sig ty `catch` \(_ :: EvalError) -> pure Nothing
--   case msubst of
--     Just (Just subst) -> displayResult x sig subst >> outputStrLn ""
--     -- Nothing -> outputStrLn "timeout"
--     _ -> pure ()

main :: IO ()
main = do
  pure ()

--   args <- getArgs
--   case args of
--     [] -> hPutStrLn stderr "Missing argument" >> exitFailure
--     path : _ -> do
--       (topEnv, sigs) <- readParsePrepare path
--       runInputT defaultSettings do
--         outputStrLn helpText
--         mainLoop topEnv sigs

-- -- FIXME: loop indefinitely if there are circular dependencies
-- prepare :: [Module] -> (TopEnv, [(QName, Raw)])
-- prepare mods = go (HM.empty, []) (HM.keys modMap)
--   where
--     modMap = HM.fromList [(m.name, m) | m <- mods]

--     go acc@(topEnv, sigs) = \case
--       [] -> (topEnv, reverse sigs)
--       m : todos ->
--         let mod' = modMap HM.! m
--             deps = mod'.imports
--          in if any (`elem` todos) deps
--               then go acc (todos ++ [m])
--               else go (goModule acc mod') todos

--     goModule acc (Module m _ decls) = foldl' (goDecl m) acc decls

--     goDecl m (topEnv, sigs) (DLet _ x a t) =
--       let topEnv' = HM.insertWith (<>) x (HM.singleton m (evaluateRaw topEnv HM.empty t)) topEnv
--           sigs' = (Qual m x, a) : sigs
--        in (topEnv', sigs')

-- readParsePrepare :: FilePath -> IO (TopEnv, [(QName, Raw)])
-- readParsePrepare libPath = do
--   fnames <- listDirectory libPath
--   let fnames' = Prelude.filter (typesExt `isExtensionOf`) fnames
--   mods <- for fnames' \fname -> do
--     src <- T.readFile (libPath </> fname)
--     either (\e -> hPutStrLn stderr (displayException e) >> exitFailure) pure $
--       parseModule fname src
--   pure $ prepare mods

-- typesExt :: String
-- typesExt = ".types"
