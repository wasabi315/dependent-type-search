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
  Foldl.foldM
    (builder `inStagesM` \b config -> indexOne config logger b)
    (primLibConfig : libraryConfigs)

loadPrimLibConfig :: IO LibraryConfig
loadPrimLibConfig = do
  path <- filePath <$> getPrimitiveLibDir
  let transparentDefPolicy = AllExcept mempty
  pure LibraryConfig {..}

indexOne :: LibraryConfig -> Logger -> TS.DbBuilder IO a -> IO a
indexOne config logger builder = withCurrentDirectory config.path do
  (Right (_, opts), _) <- pure $ runOptM $ parseBackendOptions [] [] defaultOptions
  runTCMTop' do
    setCommandLineOptions =<< addTrustedExecutables opts
    AgdaLibFile {_libIncludes = paths, _libPragmas = libOpts} <-
      libToTCM (getAgdaLibFile config.path) >>= \case
        [file] -> pure file
        [] -> aegleError "No libraries found to index"
        _ -> __IMPOSSIBLE__
    checkAndSetOptionsFromPragma libOpts
    importPrimitiveModules

    files <-
      liftIO $ sort . map Find.infoPath <$> do
        foldMap (findWithInfo (pure True) (hasAgdaExtension <$> Find.filePath)) paths

    -- Files are parsed twice, but this lowers peak memory residency

    transparentDefs <- collectTransparentDefs logger config.transparentDefPolicy files

    buildDb transparentDefs files builder

--------------------------------------------------------------------------------
-- Transparent definitions

collectTransparentDefs :: Logger -> TransparentDefPolicy -> [FilePath] -> TCM (S.Set QName)
collectTransparentDefs logger policy files =
  flip Foldl.foldM files
    $ Foldl.premapM parseFile
    $ decideAllTransparencyFold logger policy

decideAllTransparencyFold ::
  Logger ->
  TransparentDefPolicy ->
  Foldl.FoldM TCM Source (S.Set QName)
decideAllTransparencyFold _ None = mempty
decideAllTransparencyFold logger (AllExcept opaques) = Foldl.FoldM step (pure mempty) done
  where
    step acc src = (acc <>) <$!> decideAllTransparency logger opaques src
    done (transps, excluded) = do
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
-- Indexing

buildDb :: S.Set QName -> [FilePath] -> TS.DbBuilder IO a -> TCM a
buildDb transparentDefs files builder =
  flip Foldl.foldM files
    $ Foldl.premapM (parseFile >=> extractFragment transparentDefs)
    $ Foldl.hoists liftIO builder

extractFragment :: S.Set QName -> Source -> TCM TS.LibraryFragment
extractFragment transparentDefs src = withModuleInfo src \modInfo -> do
  -- cubical is not yet supported
  ifJustM (useTC (stPragmaOptions . lensOptCubical)) (\_ -> pure mempty) do
    runTransl Transl.Config {..} do
      translateScope modInfo.miInterface.iInsideScope

--------------------------------------------------------------------------------

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

inStagesM ::
  (Applicative m) =>
  Foldl.FoldM m a r ->
  (forall x. Foldl.FoldM m a x -> b -> m x) ->
  Foldl.FoldM m b r
Foldl.FoldM step begin done `inStagesM` runStage =
  Foldl.FoldM (\x -> runStage (Foldl.FoldM step (pure x) pure)) begin done
