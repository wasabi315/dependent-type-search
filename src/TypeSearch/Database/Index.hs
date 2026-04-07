{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module TypeSearch.Database.Index where

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Library
import Agda.Interaction.Options
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal hiding (arity)
import Agda.Syntax.Internal.Defs
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad (getCurrentScope)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute as Agda
import Agda.TypeChecking.Telescope
import Agda.Utils.FileName
import Agda.Utils.IO.Directory
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Monad
import Control.Monad.Except (throwError)
import Control.Monad.Reader
import Data.HashSet qualified as HS
import Data.List (sort)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.String
import System.Directory
import System.FilePath.Find qualified as Find
import TypeSearch.Common qualified as TS
import TypeSearch.Database.Feature qualified as TS
import TypeSearch.Database.Index.Common
import TypeSearch.Database.Index.Name
import TypeSearch.Database.Index.Term
import TypeSearch.Database.PostgreSQL qualified as TS
import TypeSearch.Term qualified as TS

--------------------------------------------------------------------------------
-- Utils

dbItem :: TS.QName -> TS.Term -> Maybe TS.Term -> TS.DbItem
dbItem name_qual sig body = TS.DbItem {..}
  where
    name_unqual = name_qual.name
    modul = name_qual.moduleName
    return_type_head = TS.computeReturnTypeHead sig
    polymorphic = TS.computePolymorphic sig
    TS.Arity arity_has_var arity = TS.computeArity sig

--------------------------------------------------------------------------------
-- Entrypoint

translateLibrary :: IndexConfig -> IO ()
translateLibrary config = do
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
    let env = initIndexEnv config
    libDirPrim <- useTC stPrimitiveLibDir
    files <-
      Data.List.sort . map Find.infoPath . concat <$> forM (filePath libDirPrim : paths) \path ->
        liftIO $ findWithInfo (pure True) (hasAgdaExtension <$> Find.filePath) path

    forM_ files \inputFile -> do
      path <- liftIO (absolute inputFile)
      sf <- srcFromPath path
      src <- parseSource sf
      let m = srcModuleName src
      setCurrentRange (beginningOfFile path) do
        checkModuleName m (srcOrigin src) Nothing
        withCurrentModule noModuleName $
          withTopLevelModule m $ do
            mi <- getNonMainModuleInfo m (Just src)
            setInterface mi.miInterface
            mod' <- withScope_ mi.miInterface.iInsideScope do
              runReaderT (translateInterface mi.miInterface) env
            liftIO $ TS.saveManyItems config.databaseConnection mod'

--------------------------------------------------------------------------------
-- Module translation

translateInterface :: Interface -> M [TS.DbItem]
translateInterface intf = do
  scope <- lift getCurrentScope
  let names = namesInScope [PublicNS] scope :: NamesInScope
      xns = [(x, n.anameName) | (x, ns) <- Map.toList names, n <- NonEmpty.toList ns]
  concat <$> forM xns \(cname, origQName) ->
    getConstInfo' origQName >>= \case
      Left _ -> pure []
      Right def -> do
        let outMod = translateModuleName intf.iModuleName
            outName = TS.QName outMod (translateName cname)
        translateDefinition outName def

--------------------------------------------------------------------------------
-- Definition translation

translateDefinition :: TS.QName -> Definition -> M [TS.DbItem]
translateDefinition qname def = setCurrentRangeQ def.defName $ resolvingAliasNames do
  ifM
    (orM [isErasable def.defType, isDeprecated def.defName])
    do pure []
    case def.theDef of
      AxiomDefn {} -> pure <$> translateToAxiom qname def.defType
      AbstractDefn {} -> pure <$> translateToAxiom qname def.defType
      FunctionDefn {} -> translateFunDef qname def
      DatatypeDefn {} -> pure <$> translateToAxiom qname def.defType
      RecordDefn {} -> pure <$> translateToAxiom qname def.defType
      ConstructorDefn {} -> pure <$> translateToAxiom qname def.defType
      PrimitiveDefn {} -> pure <$> translateToAxiom qname def.defType
      DataOrRecSigDefn {} -> pure []
      GeneralizableVar {} -> pure []
      PrimitiveSortDefn {} -> pure []

getDefNames :: (GetDefs a) => a -> M (HS.HashSet TS.Name)
getDefNames x = do
  unwanted <-
    traverse
      (fmap prettyShow . getBuiltinName_)
      [BuiltinLevel]
  let ns =
        getDefs'
          (const Nothing)
          ( \n ->
              if prettyShow n `elem` unwanted
                then mempty
                else HS.singleton (translateQName n).name
          )
          x
  pure ns

translateToAxiom :: TS.QName -> Type -> M TS.DbItem
translateToAxiom x ty = do
  ty <- translateType ty
  pure $! dbItem x ty Nothing

translateFunDef :: TS.QName -> Definition -> M [TS.DbItem]
translateFunDef qname def = do
  ifM
    (isAlias def.defName)
    do translateTransparent qname def
    do pure <$> translateToAxiom qname def.defType

--------------------------------------------------------------------------------
-- Translate transparent functions

hasLocalDefs :: Definition -> M Bool
hasLocalDefs def = do
  defs <- curDefs
  let locals =
        takeWhile (isAnonymousModuleName . qnameModule) $
          dropWhile (<= def.defName) $
            map fst $
              sortDefs defs
  pure $! not (null locals)

isProjectionLike :: Definition -> M Bool
isProjectionLike def = do
  let Function {..} = def.theDef
  case funProjection of
    Left {} -> pure False
    Right {} -> pure True

translateTransparent :: TS.QName -> Definition -> M [TS.DbItem]
translateTransparent qname def = do
  let Function {..} = def.theDef

  -- validation
  let bad x = translateError $ vcat [prettyTCM def.defName, x]
  whenM (hasLocalDefs def) do
    void $ bad "Not supported: transparent definition with where clause"
  whenM (isProjectionLike def) do
    void $ bad "Work-in-progress: translate projection-like definition"
  Clause {..} <- case funClauses of
    [cl] -> pure cl
    _ -> bad "Not supported: transparent definition with several clauses"

  funTy <- translateType def.defType
  fun <- translatePatternArgs def.defType namedClausePats \ty ->
    translateTerm ty (fromMaybe __IMPOSSIBLE__ clauseBody)
  let item = dbItem qname funTy (Just fun)
  pure [item]

translatePatternArgs :: Type -> NAPs -> (Type -> M TS.Term) -> M TS.Term
translatePatternArgs = \cases
  ty [] k -> k ty
  ty ((namedArg -> (VarP _ x)) : ps) k -> do
    (dom, cod) <- mustBePi ty
    let varName = realName x.dbPatVarName
        ctxElt = (KeepNames varName, dom)
    ifM
      (isErasable dom.unDom)
      do addContext ctxElt $ translatePatternArgs (absBody cod) ps k
      do
        addContextAndRenaming ctxElt $
          TS.Lam (fromString varName) <$> translatePatternArgs (absBody cod) ps k
  _ _ _ -> translateError "Not supported: transparent definition by pattern-matching"
