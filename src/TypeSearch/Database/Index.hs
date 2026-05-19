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
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Internal hiding (arity)
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad (getCurrentScope, getNamedScope, isDatatypeModule)
import Agda.TypeChecking.Pretty
import Agda.Utils.FileName
import Agda.Utils.IO.Directory
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (ifJustM)
import Agda.Utils.Monad hiding (unless)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import Database.PostgreSQL.Simple
import System.Directory
import System.FilePath.Find qualified as Find
import TypeSearch.Core.Evaluation qualified as TS
import TypeSearch.Core.Isomorphism qualified as TS
import TypeSearch.Core.Name qualified as TS
import TypeSearch.Core.Term qualified as TS
import TypeSearch.Database.Feature qualified as TS
import TypeSearch.Database.Index.Common
import TypeSearch.Database.Index.Definition
import TypeSearch.Database.Index.Name
import TypeSearch.Database.PostgreSQL qualified as TS
import TypeSearch.Prelude
import TypeSearch.Pretty qualified as TS

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
                        Nothing -> translateError $ vcat [text "Couldn't find definition", text $ show x]
                        Just x -> pure x
                    pure (foldr S.insert resolved resolved', unresolved')
        )
        (mempty, S.toList config.transparentDefNames)
        files

    unless (null unresolved) do
      translateError $ vcat [text "Couldn't find definitions", text $ show unresolved]

    let env = IndexEnv transparentDefNames 0 mempty False

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
              runReaderT (translateInterface mi.miInterface) env
            liftIO $ TS.saveManyItems config.dbConn mod'

--------------------------------------------------------------------------------
-- Module translation

translateInterface :: Interface -> M [TS.DbItem]
translateInterface intf =
  ifJustM (useTC (stPragmaOptions . lensOptCubical)) (\_ -> pure []) do
    let go :: Scope -> TCM [(C.QName, QName)]
        go scope =
          isDatatypeModule scope.scopeName >>= \case
            Just IsDataModule -> pure mempty
            _ -> do
              let ns = thingsInScope [PublicNS] scope
              Compose sub <-
                traverse
                  (go <=< getNamedScope . amodName)
                  (Compose ns.nsModules)
              let xns =
                    [ (C.QName x, n.anameName)
                    | (x, ns) <- M.toList ns.nsNames,
                      n <- NE.toList ns
                    ]
                  xns' = M.foldMapWithKey (foldMap . map . first . C.Qual) sub
              pure $ xns <> xns'

    names <- lift $ go =<< getCurrentScope
    forMaybe names \(cname, origQName) ->
      getConstInfo' origQName >>= \case
        Left _ -> pure Nothing
        Right def -> do
          let outName = translateConcreteQName (translateModuleName intf.iModuleName) cname
          mdef <- translateDefinition outName def
          for mdef $ constructDbItem def.defType

constructDbItem :: Type -> TS.Definition -> M TS.DbItem
constructDbItem origSig (TS.Definition {name = nameQual, ..}) = do
  -- FIXME: unqualify all top-level names in origSigText
  origSigText <- T.show <$> inTopContext (prettyTCM origSig)
  pure TS.DbItem {..}
  where
    nameUnqual = nameQual.name
    modul = nameQual.moduleName
    sigText = T.pack $ TS.prettyTerm0 TS.Qualify sig ""
    (sig', _) = TS.normalise0 TS.emptyMetaCtx mempty sig
    TS.Feature {arity = TS.Arity {hasVar = arityHasVar, ..}, ..} =
      TS.computeFeature sig'
