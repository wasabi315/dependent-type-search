module Main (main) where

import Control.Monad
import Control.Monad.Except
import Data.Foldable
import Data.HashMap.Lazy qualified as HM
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Traversable
import System.Console.Haskeline
import System.Environment
import System.Exit (exitFailure)
import System.IO
import System.Timeout
import TypeSearch.Common
import TypeSearch.Error
import TypeSearch.Evaluation
import TypeSearch.Parser
import TypeSearch.Pretty
import TypeSearch.Raw
import TypeSearch.UnificationModulo

orDie :: ExceptT Error IO a -> IO a
orDie (ExceptT m) =
  m >>= \case
    Left (ParseError {}) -> do
      hPutStrLn stderr "Parse error"
      exitFailure
    Right a -> pure a

main :: IO ()
main = do
  libPaths <- getArgs
  mods <- orDie $ for libPaths \path -> do
    src <- liftIO $ T.readFile path
    ExceptT $ pure $ parseModule path src
  let (topEnv, sigs) = prepare mods

  runInputT defaultSettings do
    fix \loop -> do
      minput <- getInputLine "> "
      case minput of
        Nothing -> loop
        Just ":q" -> pure ()
        Just input -> do
          case parseRaw "" (T.pack input) of
            Left _ -> do
              outputStrLn "Parse error"
              loop
            Right ty -> do
              let vty = evaluateRaw topEnv mempty ty
              for_ sigs \(x, sig) -> do
                let vsigs = instantiateRaw @[] topEnv sig
                for_ vsigs \vsig -> do
                  msubst <- liftIO $ timeout 1000 $ unifyValue topEnv vsig vty
                  case msubst of
                    Just (Just subst) -> do
                      outputStrLn $ show x ++ " : " ++ prettyRaw 0 sig ""
                      when (HM.size subst > 0) do
                        outputStrLn $ "  by instantiating " ++ prettyMetaSubst subst ""
                    _ -> pure ()
              loop

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
