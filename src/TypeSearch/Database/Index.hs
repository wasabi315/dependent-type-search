{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module TypeSearch.Database.Index
  ( indexLibrary,
    Config (..),
  )
where

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Library
import Agda.Interaction.Options
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Position
import Agda.Utils.FileName
import Agda.Utils.IO.Directory
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (ifJustM)
import Agda.Utils.Monad hiding (unless)
import Data.Set qualified as S
import Database.PostgreSQL.Simple
import System.Directory
import System.FilePath.Find qualified as Find
import TypeSearch.AgdaUtils
import TypeSearch.Core.Evaluation qualified as TS
import TypeSearch.Core.Isomorphism qualified as TS
import TypeSearch.Core.Module qualified as TS
import TypeSearch.Core.Name qualified as TS
import TypeSearch.Database.Feature qualified as TS
import TypeSearch.Database.PostgreSQL qualified as TS
import TypeSearch.Prelude
import TypeSearch.Translate.Module
import TypeSearch.Translate.Monad

--------------------------------------------------------------------------------
-- Entrypoint

data Config = Config
  { -- | Set of fully-qualified definition names subject to definition unfolding during search.
    transparentDefNames :: S.Set TS.QName,
    -- | Path to Agda library.
    libraryDir :: FilePath,
    -- | Connection to database.
    dbConn :: Connection
  }

-- TODO: make indexer an Agda backend

indexLibrary :: Config -> IO ()
indexLibrary config = do
  TS.migrate config.dbConn
  setCurrentDirectory config.libraryDir
  (Right (_, opts), _) <- pure $ runOptM $ parseBackendOptions [] [] defaultOptions
  runTCMTop' do
    opts <- addTrustedExecutables opts
    setCommandLineOptions opts
    cwd <- liftIO getCurrentDirectory
    ls <- libToTCM $ getAgdaLibFile cwd
    AgdaLibFile
      { _libIncludes = paths,
        _libPragmas = libOpts
      } <- case ls of
      [l] -> pure l
      [] -> throwError $ GenericException "No library found to build"
      _ -> __IMPOSSIBLE__
    checkAndSetOptionsFromPragma libOpts
    importPrimitiveModules
    libDirPrim <- useTC stPrimitiveLibDir
    files <-
      liftIO
        $ sort
        . map Find.infoPath
        . concat
        <$> forM (filePath libDirPrim : paths) (findWithInfo (pure True) (hasAgdaExtension <$> Find.filePath))

    -- resolve transparent definition names
    -- FIXME: make this more sensible. traversing entire library twice currently.
    (transparentDefNames, unresolved) <-
      foldM
        ( \(resolved, unresolved) inputFile -> do
            path <- liftIO (absolute inputFile)
            sf <- srcFromPath path
            src <- parseSource sf
            let m = srcModuleName src
            setCurrentRange (beginningOfFile path) do
              checkModuleName m (srcOrigin src) Nothing
              withCurrentModule noModuleName
                $ withTopLevelModule m
                $ do
                  mi <- getNonMainModuleInfo m (Just src)
                  setInterface mi.miInterface
                  withScope_ mi.miInterface.iInsideScope do
                    let mname = prettyShow mi.miInterface.iTopLevelModuleName
                        (toResolve, unresolved') = partition ((mname ==) . show . (.moduleName)) unresolved
                    resolved' <- forM toResolve \x ->
                      resolveDefinedName (show x.name) >>= \case
                        Nothing -> throwError $ GenericException $ "Couldn't find definition " ++ show x
                        Just x -> pure x
                    pure (foldr S.insert resolved resolved', unresolved')
        )
        (mempty, S.toList config.transparentDefNames)
        files

    unless (null unresolved) do
      throwError $ GenericException $ "Couldn't find definitions " ++ show unresolved

    forM_ files \inputFile -> do
      path <- liftIO (absolute inputFile)
      sf <- srcFromPath path
      src <- parseSource sf
      let m = srcModuleName src
      setCurrentRange (beginningOfFile path) do
        checkModuleName m (srcOrigin src) Nothing
        withCurrentModule noModuleName
          $ withTopLevelModule m
          $ do
            mi <- getNonMainModuleInfo m (Just src)
            setInterface mi.miInterface
            mod' <- withScope_ mi.miInterface.iInsideScope do
              runTransl transparentDefNames do
                translateInterface mi.miInterface
            liftIO $ TS.saveManyItems config.dbConn mod'

--------------------------------------------------------------------------------

translateInterface :: Interface -> Transl [TS.DbItem]
translateInterface intf =
  ifJustM (useTC (stPragmaOptions . lensOptCubical)) (\_ -> pure []) do
    modul <- translateScope intf.iInsideScope
    pure $ constructDbItem <$> modul.definitions

constructDbItem :: TS.Definition -> TS.DbItem
constructDbItem (TS.Definition {name = nameQual, ..}) = do
  TS.DbItem {..}
  where
    nameUnqual = nameQual.name
    modul = nameQual.moduleName
    (sig', _) = TS.normalise0 TS.emptyMetaCtx mempty sig
    TS.Feature {arity = TS.Arity {hasVar = arityHasVar, ..}, ..} =
      TS.feature sig'
