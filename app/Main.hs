module Main (main) where

import Control.Monad
import Control.Monad.Except
import Data.Foldable
import Data.HashMap.Lazy qualified as HM
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Traversable
import Numeric.Natural
import System.Console.Haskeline
import System.Environment
import System.Exit (exitFailure)
import System.IO
import System.Timeout
import Text.Read
import TypeSearch.Common
import TypeSearch.Error
import TypeSearch.Evaluation
import TypeSearch.Parser
import TypeSearch.Pretty
import TypeSearch.Raw
import TypeSearch.Term
import TypeSearch.UnificationModulo

orDie :: ExceptT Error IO a -> IO a
orDie (ExceptT m) =
  m >>= \case
    Left (ParseError {}) -> do
      hPutStrLn stderr "Parse error"
      exitFailure
    Right a -> pure a

data Generalise = Generalise | NoGeneralise

data Options = Options
  { generalise :: Generalise,
    modulo :: Modulo,
    timeout :: Int
  }

data Command
  = Continue
  | Help
  | Quit
  | SetOption (Options -> Options)
  | Search Raw

parseCommand :: Maybe String -> Either String Command
parseCommand = maybe (pure Continue) \input -> case words input of
  ":help" : _ -> pure Help
  ":h" : _ -> pure Help
  ":quit" : _ -> pure Quit
  ":q" : _ -> pure Quit
  ":set" : rest -> SetOption <$> parseOption rest
  (':' : cmd) : _ -> Left $ "Unknown command: " <> cmd
  _ -> case parseRaw "interactive" (T.pack input) of
    Left _ -> Left "Parse error"
    Right ty -> pure $ Search ty

parseOption :: [String] -> Either String (Options -> Options)
parseOption = \case
  [] -> pure id
  "generalise" : rest -> do
    f <- parseOption rest
    pure \o -> f o {generalise = Generalise}
  "no-generalise" : rest -> do
    f <- parseOption rest
    pure \o -> f o {generalise = NoGeneralise}
  "modulo-iso" : rest -> do
    f <- parseOption rest
    pure \o -> f o {modulo = BetaEtaIso}
  "no-modulo-iso" : rest -> do
    f <- parseOption rest
    pure \o -> f o {modulo = BetaEta}
  "timeout" : ms : rest -> case readMaybe @Natural ms of
    Nothing -> Left $ "Invalid timeout: " <> ms
    Just ms' -> do
      f <- parseOption rest
      pure \o -> f o {timeout = fromIntegral ms'}
  tok : _ -> Left $ "Unknown option: " <> tok

defaultOptions :: Options
defaultOptions =
  Options
    { generalise = NoGeneralise,
      modulo = BetaEtaIso,
      timeout = 1
    }

helpText :: String
helpText =
  unlines
    [ "TypeSearch",
      "  Type-directed search for dependent types",
      "",
      "Commands:",
      "  :help, :h      : show this help text",
      "  :quit, :q      : quit the program",
      "  :set <option>  : set an option",
      "  <type>         : search for a type signature",
      "",
      "Options:",
      "  generalise     : enable search up to generalisation",
      "  no-generalise  : disable search up to generalisation",
      "  modulo-iso     : enable search modulo βη and type isomorphisms",
      "  no-modulo-iso  : search modulo βη",
      "  timeout <ms>   : set the timeout in milliseconds"
    ]

mainLoop :: TopEnv -> [(QName, Raw)] -> InputT IO ()
mainLoop topEnv sigs = go defaultOptions
  where
    go opts = do
      input <- getInputLine "> "
      case parseCommand input of
        Left err -> do
          outputStrLn err
          go opts
        Right Continue -> go opts
        Right Help -> do
          outputStrLn helpText
          go opts
        Right Quit -> outputStrLn "Bye!"
        Right (SetOption f) -> go (f opts)
        Right (Search ty) -> do
          search topEnv sigs ty opts
          go opts

search :: TopEnv -> [(QName, Raw)] -> Raw -> Options -> InputT IO ()
search topEnv sigs ty opts = do
  let ~vty = evaluateRaw topEnv mempty ty
  for_ sigs \(x, sig) -> do
    msubst <- liftIO $ timeout (opts.timeout * 1000) do
      let vsig = evaluateRaw topEnv mempty sig
      unifyValue opts.modulo topEnv vsig vty
    case msubst of
      Just (Just subst) -> do
        let subst' = flip HM.filterWithKey subst \k _ -> case k of Src _ -> True; Gen _ -> False
        outputStrLn $ shows x $ showString " : " $ prettyRaw 0 sig ""
        when (HM.size subst' > 0) do
          outputStrLn $ "  by instantiating " ++ prettyMetaSubst subst' "\n"
      _ -> pure ()

main :: IO ()
main = do
  libPaths <- getArgs
  mods <- orDie $ for libPaths \path -> do
    src <- liftIO $ T.readFile path
    ExceptT $ pure $ parseModule path src
  let (topEnv, sigs) = prepare mods

  runInputT defaultSettings do
    outputStrLn helpText
    mainLoop topEnv sigs

-- runInputT defaultSettings do
--   fix \loop -> do
--     minput <- getInputLine "> "
--     case minput of
--       Nothing -> loop
--       Just ":q" -> pure ()
--       Just input -> do
--         case parseRaw "" (T.pack input) of
--           Left _ -> do
--             outputStrLn "Parse error"
--             loop
--           Right ty -> do
--             let vty = evaluateRaw topEnv mempty ty
--             for_ sigs \(x, sig) -> do
--               let vsigs = instantiateRaw @[] topEnv sig
--               for_ vsigs \vsig -> do
--                 msubst <- liftIO $ timeout 100000 $ unifyValue BetaEtaIso topEnv vsig vty
--                 case msubst of
--                   Just (Just subst) -> do
--                     let subst' =
--                           subst
--                             & HM.filterWithKey (\k _ -> case k of Src _ -> True; Gen _ -> False)
--                             & HM.mapKeys
--                               ( \case
--                                   Gen _ -> error "impossible"
--                                   Src (Name n)
--                                     | T.last n == '?' -> Src (Name $ T.init n)
--                                     | otherwise -> Src (Name n)
--                               )
--                     outputStrLn $ show x ++ " : " ++ prettyRaw 0 sig ""
--                     when (HM.size subst' > 0) do
--                       outputStrLn $ "  by instantiating " ++ prettyMetaSubst subst' ""
--                   _ -> pure ()
--             loop

-- FIXME: loop indefinitely if there are circular dependencies
prepare :: [Module] -> (TopEnv, [(QName, Raw)])
prepare mods = go (HM.empty, []) (HM.keys modMap)
  where
    modMap = HM.fromList [(m.name, m) | m <- mods]

    go acc@(topEnv, sigs) = \case
      [] -> (topEnv, reverse sigs)
      m : todos ->
        let mod' = modMap HM.! m
            deps = mod'.imports
         in if any (`elem` todos) deps
              then go acc (todos ++ [m])
              else go (goModule acc mod') todos

    goModule acc (Module m _ decls) = foldl' (goDecl m) acc decls

    goDecl m acc@(topEnv, sigs) = \case
      DLoc (d :@ _) -> goDecl m acc d
      DLet x a t ->
        let topEnv' = HM.insertWith (<>) x (HM.singleton m (evaluateRaw topEnv HM.empty t)) topEnv
            sigs' = (Qual m x, a) : sigs
         in (topEnv', sigs')

instantiate :: (MonadPlus m) => TopEnv -> Value -> m Value
instantiate topEnv = \case
  VPi (Name x) _ b -> do
    let m = Src (Name $ x <> "?") -- append ? back to the name so it will be fresh
    pure $ instantiate' $ b (VMetaApp m [])
  VArr a b -> pure $ VArr a (instantiate' b)
  VTop _ _ vs -> do
    (_, v) <- choose vs
    instantiate topEnv v
  t -> pure t

instantiate' :: Value -> Value
instantiate' = \case
  VPi (Name x) _ b ->
    -- throwing away the domain type currently
    let m = Src (Name $ x <> "?") -- append ? back to the name so it will be fresh
     in instantiate' $ b (VMetaApp m [])
  VArr a b -> VArr a (instantiate' b)
  t -> t

instantiateRaw :: (MonadPlus m) => TopEnv -> Raw -> m Value
instantiateRaw topEnv = instantiate topEnv . evaluateRaw topEnv mempty
