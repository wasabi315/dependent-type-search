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
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Internal hiding (arity)
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad (getCurrentScope, getNamedScope, isDatatypeModule)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute as Agda
import Agda.TypeChecking.Telescope
import Agda.Utils.FileName
import Agda.Utils.IO.Directory
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Maybe (ifJustM)
import Agda.Utils.Monad
import Control.Monad.Except (throwError)
import Control.Monad.Reader
import Data.Bifunctor
import Data.Functor.Compose
import Data.List (partition, sort)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set qualified as Set
import Data.String
import Data.Text qualified as T
import System.Directory
import System.FilePath.Find qualified as Find
import TypeSearch.Common qualified as TS
import TypeSearch.Database.Feature qualified as TS
import TypeSearch.Database.Index.Common
import TypeSearch.Database.Index.Name
import TypeSearch.Database.Index.Term
import TypeSearch.Database.PostgreSQL qualified as TS
import TypeSearch.Evaluation qualified as TS
import TypeSearch.Pretty qualified as TS
import TypeSearch.Term qualified as TS

--------------------------------------------------------------------------------
-- Utils

dbItem :: TS.QName -> TS.Type -> TS.Type -> Maybe TS.Term -> TS.DbItem
dbItem name_qual sig origSig body = TS.DbItem {..}
  where
    name_unqual = name_qual.name
    modul = name_qual.moduleName
    sig_text = T.pack $ TS.prettyTerm0 TS.Qualify sig ""
    original_sig_text = T.pack $ TS.prettyTerm0 TS.Unqualify origSig ""
    (sig', _) = TS.normalise0 TS.emptyMetaCtx mempty sig
    return_type_head = TS.computeReturnTypeHead sig'
    polymorphic = TS.computePolymorphic sig'
    TS.Arity arity_has_var arity = TS.computeArity sig'

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
    libDirPrim <- useTC stPrimitiveLibDir
    files <-
      liftIO $
        Data.List.sort . map Find.infoPath . concat <$> forM (filePath libDirPrim : paths) (findWithInfo (pure True) (hasAgdaExtension <$> Find.filePath))

    -- alias resolution
    (aliasNames, unresolved) <-
      foldM
        ( \(resolved, unresolved) inputFile -> do
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
                  withScope_ mi.miInterface.iInsideScope do
                    let mname = prettyShow mi.miInterface.iTopLevelModuleName
                        (toResolve, unresolved') = partition ((mname ==) . show . (.moduleName)) unresolved
                    resolved' <- forM toResolve \x ->
                      resolveDefinedName (show x.name) >>= \case
                        Nothing -> translateError $ vcat [text "Couldn't find definition", text $ show x]
                        Just x -> pure x
                    pure (foldr Set.insert resolved resolved', unresolved')
        )
        (mempty, Set.toList config.aliasNames)
        files

    unless (null unresolved) do
      translateError $ vcat [text "Couldn't find definitions", text $ show unresolved]

    let env = IndexEnv aliasNames 0 mempty False

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
                    | (x, ns) <- Map.toList ns.nsNames,
                      n <- NonEmpty.toList ns
                    ]
                  xns' = Map.foldMapWithKey (foldMap . map . first . C.Qual) sub
              pure $ xns <> xns'

    names <- lift $ go =<< getCurrentScope
    concat <$> forM names \(cname, origQName) ->
      getConstInfo' origQName >>= \case
        Left _ -> pure []
        Right def -> do
          let outName = translateConcreteQName (translateModuleName intf.iModuleName) cname
          translateDefinition outName def

--------------------------------------------------------------------------------
-- Definition translation

translateDefinition :: TS.QName -> Definition -> M [TS.DbItem]
translateDefinition qname def = setCurrentRangeQ def.defName do
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

translateToAxiom :: TS.QName -> Type -> M TS.DbItem
translateToAxiom x ty = do
  origTy <- translateType ty
  ty <- locallyReduceAlias $ translateType ty
  pure $! dbItem x ty origTy Nothing

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

  origFunTy <- translateType def.defType
  funTy <- locallyReduceAlias $ translateType def.defType
  fun <- locallyReduceAlias $ translatePatternArgs def.defType namedClausePats \ty ->
    translateTerm ty (fromMaybe __IMPOSSIBLE__ clauseBody)
  let item = dbItem qname funTy origFunTy (Just fun)
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
