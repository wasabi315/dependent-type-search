module Main where

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
import TypeSearch.Term
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
              let ty' = rawToTerm topEnv ty
              for_ sigs \(x, sig) -> do
                let sig' = instantiate topEnv ty' sig
                msubst <- liftIO $ timeout 500000 $ unifyTerm topEnv sig' ty'
                case msubst of
                  Nothing -> outputStrLn $ "timeout for " ++ show x
                  Just Nothing -> pure ()
                  Just (Just subst) -> do
                    outputStrLn $ show x ++ " : " ++ prettyRaw 0 sig ""
                    when (HM.size subst > 0) do
                      outputStrLn $ "  by instantiating " ++ prettyMetaSubst subst ""
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

rawToTerm :: TopEnv -> Raw -> Term
rawToTerm topEnv = quote 0 . evaluateRaw topEnv mempty

instantiate :: TopEnv -> Term -> Raw -> Term
instantiate topEnv query sig = bar $ quote n $ baz $ evaluateRaw topEnv mempty sig
  where
    foo = \case
      Pi x a b
        | x /= "_" ->
            let (f, i) = foo b
             in (Pi x a . f, i + 1)
      _ -> (id, Level 0)

    (bar, n) = foo query

    args = map VVar [0 .. n - 1]

    baz = \case
      VPi x _ b -- Throwing away the domain type currently
        | x /= "_" -> baz (b $ VMetaApp (Src x) args)
      VTop _ _ [(_, t)] -> baz t
      t -> t
