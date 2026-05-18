{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module TypeSearch.Database.Index
  ( indexLibrary,
    IndexConfig (..),
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
import Data.IORef
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
import TypeSearch.Database.Index.Name
import TypeSearch.Database.Index.Term
import TypeSearch.Database.Index.TransparentDef
import TypeSearch.Database.PostgreSQL qualified as TS
import TypeSearch.Prelude
import TypeSearch.Pretty qualified as TS

--------------------------------------------------------------------------------
-- Entrypoint

data IndexConfig = IndexConfig
  { -- | Set of fully-qualified definition names subject to definition unfolding during search.
    transparentDefNames :: S.Set TS.QName,
    -- | Path to Agda library.
    libraryDirectory :: FilePath,
    -- | Connection to database.
    databaseConnection :: Connection
  }

data IndexBackendEnv = IndexBackendEnv
  { indexEnv :: IndexEnv,
    indexConfig :: IndexConfig,
    indexedModulesRef :: IORef (S.Set TopLevelModuleName)
  }

indexBackend :: IndexConfig -> IndexEnv -> IORef (S.Set TopLevelModuleName) -> Backend
indexBackend config env indexedModulesRef =
  Backend
    $ Backend'
      { backendName = "dependent-type-search",
        backendVersion = Nothing,
        options = (),
        commandLineFlags = mempty,
        isEnabled = const True,
        preCompile = const $ pure $ IndexBackendEnv env config indexedModulesRef,
        postCompile = \_ _ _ -> pure (),
        preModule = \backendEnv _ mName _ -> do
          indexed <- liftIO $ readIORef backendEnv.indexedModulesRef
          if S.member mName indexed
            then pure $ Skip ()
            else pure $ Recompile (),
        postModule = \backendEnv _ _ mName _ -> do
          mod' <- runReaderT (translateInterface =<< curIF) backendEnv.indexEnv
          liftIO $ TS.saveManyItems backendEnv.indexConfig.databaseConnection mod'
          liftIO $ modifyIORef' backendEnv.indexedModulesRef (S.insert mName)
          pure (),
        compileDef = \_ _ _ _ -> pure (),
        scopeCheckingSuffices = False,
        mayEraseType = const $ pure True,
        backendInteractTop = Nothing,
        backendInteractHole = Nothing
      }

indexLibrary :: IndexConfig -> IO ()
indexLibrary config = do
  setCurrentDirectory config.libraryDirectory
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
    indexedModulesRef <- liftIO $ newIORef mempty
    setTCLens stBackends [indexBackend config env indexedModulesRef]

    forM_ files \inputFile -> do
      path <- liftIO (absolute inputFile)
      sf <- srcFromPath path
      src <- parseSource sf
      result <- typeCheckMain TypeCheck src
      callBackend "dependent-type-search" IsMain result

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
          translateDefinition outName def

--------------------------------------------------------------------------------
-- Definition translation

translateDefinition :: TS.QName -> Definition -> M (Maybe TS.DbItem)
translateDefinition qname def = setCurrentRangeQ def.defName do
  ifM
    (orM [isErasable def.defType, isDeprecated def.defName])
    do pure Nothing
    case def.theDef of
      AxiomDefn {} -> Just <$> translateToAxiom qname def.defType
      AbstractDefn {} -> Just <$> translateToAxiom qname def.defType
      FunctionDefn {} -> Just <$> translateFunDef qname def
      DatatypeDefn {} -> Just <$> translateToAxiom qname def.defType
      RecordDefn {} -> Just <$> translateToAxiom qname def.defType
      ConstructorDefn {} -> Just <$> translateToAxiom qname def.defType
      PrimitiveDefn {} -> Just <$> translateToAxiom qname def.defType
      DataOrRecSigDefn {} -> pure Nothing
      GeneralizableVar {} -> pure Nothing
      PrimitiveSortDefn {} -> pure Nothing

translateToAxiom :: TS.QName -> Type -> M TS.DbItem
translateToAxiom x ty = do
  ty' <- locallyReduceTransparentDef $ translateType ty
  constructDbItem x ty' ty Nothing

translateFunDef :: TS.QName -> Definition -> M TS.DbItem
translateFunDef qname def = do
  ty <- locallyReduceTransparentDef $ translateType def.defType
  body <- ifM
    (isTransparentDef def.defName)
    do Just <$> translateTransparentDefBody def
    do pure Nothing
  constructDbItem qname ty def.defType body

constructDbItem :: TS.QName -> TS.Type -> Type -> Maybe TS.Term -> M TS.DbItem
constructDbItem name_qual sig origSig body = do
  -- FIXME: unqualify all top-level names
  original_sig_text <- T.show <$> inTopContext (prettyTCM origSig)
  pure TS.DbItem {..}
  where
    name_unqual = name_qual.name
    modul = name_qual.moduleName
    sig_text = T.pack $ TS.prettyTerm0 TS.Qualify sig ""
    (sig', _) = TS.normalise0 TS.emptyMetaCtx mempty sig
    return_type_head = TS.computeReturnTypeHead sig'
    polymorphic = TS.computePolymorphic sig'
    TS.Arity arity_has_var arity = TS.computeArity sig'
