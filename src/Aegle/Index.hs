{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Aegle.Index
  ( index,
    Config (..),
    LibraryConfig (..),
    TransparentDefPolicy (..),
    Logger,
  )
where

import Aegle.Database.Backend qualified as TS
import Aegle.Index.Translate (runTransl)
import Aegle.Index.Translate qualified as Transl
import Aegle.Index.Translate.Scope
import Aegle.Index.TransparentDefs
import Aegle.Index.Utils
import Aegle.Prelude
import Agda.Compiler.Backend hiding (None)
import Agda.Compiler.Common
import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Library
import Agda.Interaction.Options
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.TypeChecking.Pretty
import Agda.Utils.FileName
import Agda.Utils.IO.Directory
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (ifJustM)
import Control.Foldl qualified as Foldl
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Data.Text qualified as T
import Prettyprinter qualified as P
import Prettyprinter.Render.Terminal qualified as P
import System.Directory
import System.FilePath.Find qualified as Find

--------------------------------------------------------------------------------
-- Config

newtype Config = Config
  { libraryConfigs :: [LibraryConfig]
  }

data LibraryConfig = LibraryConfig
  { transparentDefPolicy :: TransparentDefPolicy,
    path :: FilePath
  }

--------------------------------------------------------------------------------
-- Logger

type Logger = "logName" :? T.Text -> P.Doc P.AnsiStyle -> IO ()

--------------------------------------------------------------------------------

-- TODO: make indexer an Agda backend when Agda supports --build-library for arbitrary backend

-- Entrypoint
index :: Config -> Logger -> TS.DbBuilder IO a -> IO a
index Config {..} logger builder = do
  primLibConfig <- liftIO loadPrimLibConfig
  let libConfigs = primLibConfig : libraryConfigs
  -- each library is traversed twice for lower memory residency
  (transparentDefs, moduleOrigins) <-
    flip foldMap libConfigs \config -> foldLibrarySources config.path do
      (,)
        <$> collectTransparentDefs logger config.transparentDefPolicy
        <*> collectModuleOrigins
  let config = Transl.Config {..}
  builder <-
    foldM
      ( \builder libConfig -> foldLibrarySources libConfig.path do
          Foldl.premapM (translate config) do
            Foldl.hoists liftIO (Foldl.duplicateM builder)
      )
      builder
      libConfigs
  extractM builder

loadPrimLibConfig :: IO LibraryConfig
loadPrimLibConfig = do
  path <- filePath <$> getPrimitiveLibDir
  let transparentDefPolicy = AllExcept mempty
  pure LibraryConfig {..}

--------------------------------------------------------------------------------
-- Module provenance

collectModuleOrigins :: Foldl.FoldM TCM Source (M.Map TopLevelModuleName LibName)
collectModuleOrigins = flip foldMapM pure \src ->
  withModuleInfo src \_ -> do
    -- cubical is not yet supported
    ifJustM (useTC (stPragmaOptions . lensOptCubical)) (\_ -> pure mempty) do
      let libName = case src.srcProjectLibs of
            [libFile] -> libFile._libName
            _ -> error "TODO: decideNameOrigin"
      pure $! M.singleton src.srcModuleName libName

--------------------------------------------------------------------------------
-- Transparent definitions

collectTransparentDefs ::
  Logger ->
  TransparentDefPolicy ->
  Foldl.FoldM TCM Source (S.Set QName)
collectTransparentDefs logger = \case
  None -> mempty
  AllExcept opaques ->
    foldMapM (decideAllTransparency logger opaques) \(transps, excluded) -> do
      let unmatched = opaques S.\\ S.map (T.pack . prettyShow) excluded
      unless (S.null unmatched) do
        aegleWarning
          $ vsep ["Unmatched exclusions found", prettyList_ (pretty <$> S.toList unmatched)]
      pure transps

decideAllTransparency ::
  Logger ->
  OpaqueDefNames ->
  Source ->
  TCM (S.Set QName, S.Set QName)
decideAllTransparency logger opaques src = withModuleInfo src \modInfo -> do
  -- cubical is not yet supported
  ifJustM (useTC (stPragmaOptions . lensOptCubical)) (\_ -> pure mempty) do
    -- TODO: share pubNames with decideNameOriginFold?
    let pubNames = collectPublicNames modInfo.miInterface.iInsideScope
    flip foldMap pubNames \pubName -> do
      def <- getConstInfo pubName
      let modName = T.pack $ prettyShow modInfo.miInterface.iTopLevelModuleName
          name = T.pack $ prettyShow pubName
      decideTransparency opaques def >>= \case
        Right () -> do
          liftIO $ logTransp modName name
          pure $! S.singleton pubName // mempty
        Left reason -> do
          liftIO $ logOpaque modName name reason
          let excluded = case reason of
                ExcludedByConfig -> S.singleton pubName
                _ -> mempty
          pure (mempty, excluded)
  where
    logTransp modName name =
      logger ! #logName ("transp/" <> modName) $ P.pretty name P.<+> P.colon P.<+> "transparent"

    logOpaque modName name reason =
      logger
        ! #logName ("transp/" <> modName)
        $ ( P.pretty name
              P.<+> P.colon
              P.<+> "opaque"
              P.<+> P.parens
                ( case reason of
                    NotFunction -> "not a function"
                    ProjectionLike -> "projection-like"
                    HasLocalDefs {} -> "has local definitions"
                    PatternMatching -> "pattern-matching"
                    NoReturnSort -> "no return sort"
                    ExcludedByConfig -> "by config"
                )
          )

--------------------------------------------------------------------------------
-- Translation

translate :: Transl.Config -> Source -> TCM TS.LibraryFragment
translate config src = withModuleInfo src \modInfo -> do
  -- cubical is not yet supported
  ifJustM (useTC (stPragmaOptions . lensOptCubical)) (\_ -> pure mempty) do
    runTransl config do
      translateScope modInfo.miInterface.iInsideScope

--------------------------------------------------------------------------------
-- Utils

foldLibrarySources :: FilePath -> Foldl.FoldM TCM Source r -> IO r
foldLibrarySources libPath fold = withCurrentDirectory libPath do
  (Right (_, opts), _) <- pure $ runOptM $ parseBackendOptions [] [] defaultOptions
  runTCMTop' do
    setCommandLineOptions =<< addTrustedExecutables opts
    AgdaLibFile {_libIncludes = paths, _libPragmas = libOpts} <-
      libToTCM (getAgdaLibFile libPath) >>= \case
        [file] -> pure file
        [] -> aegleError "No libraries found to index"
        _ -> __IMPOSSIBLE__
    checkAndSetOptionsFromPragma libOpts
    importPrimitiveModules

    files <-
      liftIO $ sort . map Find.infoPath <$> do
        foldMap (findWithInfo (pure True) (hasAgdaExtension <$> Find.filePath)) paths

    flip Foldl.foldM files $ Foldl.premapM parseFile fold

parseFile :: FilePath -> TCM Source
parseFile file = do
  path <- liftIO $ absolute file
  sf <- srcFromPath path
  parseSource sf

withModuleInfo :: Source -> (ModuleInfo -> TCM r) -> TCM r
withModuleInfo src act = do
  let modName = src.srcModuleName
  withCurrentModule noModuleName do
    withTopLevelModule modName do
      modInfo <- getNonMainModuleInfo modName (Just src)
      setInterface modInfo.miInterface
      act modInfo

extractM :: (Monad m) => Foldl.FoldM m a r -> m r
extractM (Foldl.FoldM _ begin done) = begin >>= done

foldMapM :: (Monad m, Monoid w) => (a -> m w) -> (w -> m b) -> Foldl.FoldM m a b
foldMapM f g = Foldl.FoldM (\acc x -> (acc <>) <$!> f x) (pure mempty) g
