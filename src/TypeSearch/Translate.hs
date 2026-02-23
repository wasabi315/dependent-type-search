module TypeSearch.Translate (translateLibrary) where

import Agda.Compiler.Backend qualified as Agda
import Agda.Compiler.Common qualified as Agda
import Agda.Interaction.FindFile qualified as Agda
import Agda.Interaction.Imports qualified as Agda
import Agda.Interaction.Library qualified as Agda
import Agda.Interaction.Options qualified as Agda
import Agda.Syntax.Abstract.Name qualified as Agda
import Agda.Syntax.Common qualified as Agda
import Agda.Syntax.Common.Pretty qualified as Agda
import Agda.Syntax.Concrete qualified as Concrete
import Agda.Syntax.Internal qualified as Internal
import Agda.Syntax.Internal.Pattern qualified as Internal
import Agda.Syntax.Position qualified as Agda
import Agda.Syntax.Scope.Base qualified as Agda
import Agda.TypeChecking.Datatypes qualified as Agda
import Agda.TypeChecking.Level qualified as Agda
import Agda.TypeChecking.Monad.Context qualified as Agda
import Agda.TypeChecking.Pretty.Warning qualified as Agda
import Agda.TypeChecking.ProjectionLike qualified as Agda
import Agda.TypeChecking.Records qualified as Agda
import Agda.TypeChecking.Reduce qualified as Agda
import Agda.TypeChecking.Substitute qualified as Agda
import Agda.TypeChecking.Telescope qualified as Agda
import Agda.Utils.CallStack (HasCallStack)
import Agda.Utils.FileName qualified as Agda
import Agda.Utils.IO.Directory qualified as Agda
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Control.Monad (forM, forM_)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.IO.Class (liftIO)
import Data.Bifunctor
import Data.List (sort)
import Data.List.NonEmpty (toList)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set qualified as Set
import Data.String
import Data.Text qualified as T
import System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import System.FilePath (addExtension, takeDirectory, (</>))
import System.FilePath.Find qualified as Find
import System.IO (hPutStrLn, stderr)
import TypeSearch.Common
import TypeSearch.Pretty (prettyModule)
import TypeSearch.Raw

--------------------------------------------------------------------------------
-- Entrypoint

translateLibrary :: FilePath -> IO ()
translateLibrary outDir = do
  (Right (_, opts), _) <- pure $ Agda.runOptM $ Agda.parseBackendOptions [] [] Agda.defaultOptions
  Agda.runTCMTop' do
    opts <- Agda.addTrustedExecutables opts
    Agda.setCommandLineOptions opts
    cwd <- liftIO getCurrentDirectory
    ls <- Agda.libToTCM $ Agda.getAgdaLibFile cwd
    Agda.AgdaLibFile
      { _libIncludes = paths,
        _libPragmas = libOpts
      } <- case ls of
      [l] -> pure l
      [] -> throwError $ Agda.GenericException "No library found to build"
      _ -> __IMPOSSIBLE__
    Agda.checkAndSetOptionsFromPragma libOpts
    Agda.importPrimitiveModules
    files <-
      sort . map Find.infoPath . concat <$> forM paths \path ->
        liftIO $ Agda.findWithInfo (pure True) (Agda.hasAgdaExtension <$> Find.filePath) path
    forM_ files \inputFile ->
      ( do
          path <- liftIO (Agda.absolute inputFile)
          sf <- Agda.srcFromPath path
          src <- Agda.parseSource sf
          let m = Agda.srcModuleName src
          Agda.setCurrentRange (Agda.beginningOfFile path) do
            Agda.checkModuleName m (Agda.srcOrigin src) Nothing
            Agda.withCurrentModule Agda.noModuleName $
              Agda.withTopLevelModule m $ do
                mod' <- translateModule m src
                liftIO $ writeModule outDir mod'
      )
        `catchError` \err ->
          liftIO $ hPutStrLn stderr $ "Warning: " ++ show err

writeModule :: FilePath -> Module -> IO ()
writeModule outDir m = do
  let outPath = moduleOutputPath outDir m.name
  createDirectoryIfMissing True (takeDirectory outPath)
  writeFile outPath (prettyModule m "")

moduleOutputPath :: FilePath -> ModuleName -> FilePath
moduleOutputPath outDir (ModuleName mn) =
  addExtension (foldl (</>) outDir (map T.unpack (T.splitOn "." mn))) "types"

translateModule :: Agda.TopLevelModuleName -> Agda.Source -> Agda.TCM Module
translateModule m src = do
  mi <- Agda.getNonMainModuleInfo m (Just src)
  let isInfectiveWarning Agda.InfectiveImport {} = True
      isInfectiveWarning _ = False
      warns = filter (not . isInfectiveWarning . Agda.tcWarning) $ Set.toAscList $ mi.miWarnings
  Agda.tcWarningsToError warns
  translateInterface mi.miInterface

--------------------------------------------------------------------------------
-- Module translation

exportedPairs :: Agda.Interface -> [(Concrete.Name, Internal.QName)]
exportedPairs intf =
  let si = Agda.iInsideScope intf
      modName = intf.iModuleName
      mods = si._scopeModules
      mscope = Map.findWithDefault Agda.emptyScope modName mods
      exported = Agda.exportedNamesInScope mscope :: Agda.NamesInScope
   in [ (cname, Agda.anameName an)
      | (cname, ans) <- Map.toList exported,
        an <- toList ans
      ]

translateInterface :: Agda.Interface -> Agda.TCM Module
translateInterface intf = do
  let pairs = exportedPairs intf
  decls <- fmap concat $ forM pairs \(cname, origQName) ->
    ( do
        def <- Agda.getConstInfo origQName
        let outMod = translateModuleName intf.iModuleName
            outName = Qual outMod (translateName cname)
        translateDefinition outName def
    )
      `catchError` \err -> do
        liftIO $ hPutStrLn stderr $ "Warning: " ++ show err
        pure []
  let modName = translateModuleName intf.iModuleName
      imports = map (translateTopLevelModuleName . fst) intf.iImportedModules
  pure Module {name = modName, imports = imports, decls = decls}

--------------------------------------------------------------------------------
-- Definition translation

translateDefinition :: QName -> Agda.Definition -> Agda.TCM [Decl]
translateDefinition qname def =
  Agda.withCurrentModule (Agda.qnameModule def.defName) case def.theDef of
    Agda.AxiomDefn {} -> pure <$> translateIntoAxiom qname def.defType
    Agda.AbstractDefn {} -> pure <$> translateIntoAxiom qname def.defType
    Agda.FunctionDefn {} -> translateFunDef qname def
    Agda.DatatypeDefn {} -> pure <$> translateIntoAxiom qname def.defType
    Agda.RecordDefn {} -> translateRecordDef qname def
    Agda.ConstructorDefn {} -> translateConDef qname def
    Agda.PrimitiveDefn {} -> pure <$> translateIntoAxiom qname def.defType
    Agda.DataOrRecSigDefn {} -> pure []
    Agda.GeneralizableVar {} -> pure []
    Agda.PrimitiveSortDefn {} -> pure []

translateIntoAxiom :: QName -> Internal.Type -> Agda.TCM Decl
translateIntoAxiom x ty = DAxiom Nothing x <$> translateType ty

--------------------------------------------------------------------------------
-- Internal term/type → Raw

translateSpined ::
  ([Internal.Term] -> Agda.TCM Raw) ->
  (Internal.Elims -> Internal.Term) ->
  Internal.Type ->
  Internal.Elims ->
  Agda.TCM Raw
translateSpined c tm ty = \case
  [] -> c []
  e@(Internal.Proj o q) : es -> do
    let t = tm []
    ty' <- Agda.shouldBeProjectible t ty o q
    translateSpined (translateProj q ty t ty') (tm . (e :)) ty' es
  e@(Internal.Apply (Agda.unArg -> x)) : es -> do
    (_, b) <- Agda.mustBePi ty
    translateSpined (c . (x :)) (tm . (e :)) (Agda.absApp b x) es
  Internal.IApply {} : _ -> translateError "Bad spine: IApply"

translateProj ::
  Internal.QName -> Internal.Type -> Internal.Term -> Internal.Type -> [Internal.Term] -> Agda.TCM Raw
translateProj q tty t ty args = do
  let name = translateQName q
  arg <- translateTerm tty t
  translateApp (RVar name `RApp` arg) ty args

translateApp :: Raw -> Internal.Type -> [Internal.Term] -> Agda.TCM Raw
translateApp f ty args = do
  args <- translateArgs ty args
  pure $! foldl' RApp f args

translateArgs :: Internal.Type -> [Internal.Term] -> Agda.TCM [Raw]
translateArgs ty args = snd <$> translateArgs' ty args

translateArgs' :: Internal.Type -> [Internal.Term] -> Agda.TCM (Internal.Type, [Raw])
translateArgs' ty = \case
  [] -> pure (ty, [])
  (x : xs) -> do
    (a, b) <- Agda.mustBePi ty
    let rest = translateArgs' (Agda.absApp b x) xs
    canErase (Internal.unDom a) >>= \case
      True -> rest
      False -> do
        second . (:) <$> translateTerm (Internal.unDom a) x <*> rest

translateVar :: Int -> Internal.Type -> [Internal.Term] -> Agda.TCM Raw
translateVar i ty args = do
  name <- translateDBVar i
  translateApp (RVar $ Unqual name) ty args

translateDef :: Internal.QName -> Internal.Type -> [Internal.Term] -> Agda.TCM Raw
translateDef f ty args = do
  let name = translateQName f
  translateApp (RVar name) ty args

translateCon :: Internal.ConHead -> Internal.ConInfo -> Internal.Type -> [Internal.Term] -> Agda.TCM Raw
translateCon h i ty args = do
  let c = Internal.conName h
  info <- Agda.getConstInfo c
  if Agda.defCopy info
    then
      let Agda.Constructor {conSrcCon = ch'} = Agda.theDef info
       in translateCon ch' i ty args
    else do
      let name = translateQName c
      translateApp (RVar name) ty args

translateLam :: Internal.Type -> Agda.ArgInfo -> Internal.Abs Internal.Term -> Agda.TCM Raw
translateLam ty _argi abs = do
  (dom, cod) <- Agda.mustBePi ty
  let varName = Internal.absName abs
      ctxElt = (varName,) <$> dom
  RLam (fromString varName) <$> Agda.addContext ctxElt (translateTerm (Agda.absBody cod) (Agda.absBody abs))

translateTerm :: Internal.Type -> Internal.Term -> Agda.TCM Raw
translateTerm ty v = do
  v <- Agda.instantiate v
  Agda.reduceProjectionLike v >>= \case
    Internal.Sort _ -> pure RU
    Internal.Pi a b -> do
      let compileB = Agda.underAbstraction a b translateType
      translateDomType (Internal.absName b) a >>= \case
        Nothing -> compileB
        Just (x, a) -> RPi x a <$> compileB
    Internal.Var i es -> do
      ty <- Agda.typeOfBV i
      translateSpined (translateVar i ty) (Internal.Var i) ty es
    Internal.Def f es -> do
      ty <- Agda.defType <$> Agda.getConstInfo f
      translateSpined (translateDef f ty) (Internal.Def f) ty es
    Internal.Con ch ci es -> do
      Just (_, ty) <- Agda.getConType ch ty
      translateSpined (translateCon ch ci ty) (Internal.Con ch ci) ty es
    Internal.Lam v b -> translateLam ty v b
    Internal.Lit {} ->
      translateError "unimplemented: Lit"
    Internal.Level {} ->
      translateError "Bad term: Level"
    Internal.MetaV {} ->
      translateError "Bad term: MetaV"
    Internal.DontCare {} ->
      translateError "Bad term: DontCare"
    Internal.Dummy {} ->
      translateError "Bad term: Dummy"

translateType :: Internal.Type -> Agda.TCM Raw
translateType ty = translateTerm (Agda.sort $ Internal._getSort ty) $ Internal.unEl ty

translateDomType :: Agda.ArgName -> Internal.Dom Internal.Type -> Agda.TCM (Maybe (Name, Raw))
translateDomType x a =
  canErase (Internal.unDom a) >>= \case
    True -> pure Nothing
    False -> do
      a <- translateType $ Internal.unDom a
      pure $ Just (fromString x, a)

canErase :: Internal.Type -> Agda.TCM Bool
canErase a = do
  Agda.TelV tel b <- Agda.telView a
  Agda.addContext tel do
    let c = Internal.El Internal.__DUMMY_SORT__ (Internal.unEl b)
    isLevel <- Agda.isLevelType c
    isSize <- isJust <$> Agda.isSizeType c
    pure $! isLevel || isSize

translateTeleBindsToPi :: Internal.Telescope -> Agda.TCM Raw -> Agda.TCM Raw
translateTeleBindsToPi tel body = go id tel
  where
    go pis = \case
      Internal.EmptyTel -> pis <$> body
      Internal.ExtendTel a tel ->
        translateDomType (Internal.absName tel) a >>= \case
          Nothing -> Agda.underAbstraction a tel $ go pis
          Just (x, a') -> do
            Agda.underAbstraction a tel $ go (pis . RPi x a')

translateTeleBindsToLam :: Internal.Telescope -> Agda.TCM Raw -> Agda.TCM Raw
translateTeleBindsToLam tel body = go id tel
  where
    go lams = \case
      Internal.EmptyTel -> lams <$> body
      Internal.ExtendTel a tel ->
        canErase (Internal.unDom a) >>= \case
          True -> Agda.underAbstraction a tel $ go lams
          False -> do
            let x = fromString $ Internal.absName tel
            Agda.underAbstraction a tel $ go (lams . RLam x)

--------------------------------------------------------------------------------

translateRecordDef :: QName -> Agda.Definition -> Agda.TCM [Decl]
translateRecordDef qname def = do
  let Agda.Record {..} = def.theDef

  let buildSigmaChain sigmas = \cases
        [_] (Internal.ExtendTel a _) -> sigmas <$> translateType (Internal.unDom a)
        (n : ns) (Internal.ExtendTel a tel) -> do
          let x = fromString $ Agda.prettyShow $ Agda.qnameName $ Internal.unDom n
          a' <- translateType (Internal.unDom a)
          Agda.underAbstraction a tel $ buildSigmaChain (sigmas . RSigma x a') ns
        _ _ -> __IMPOSSIBLE__

  if Agda.theEtaEquality recEtaEquality' /= Agda.YesEta || null recFields
    then pure <$> translateIntoAxiom qname def.defType
    else do
      Agda.TelV tel _ <- Agda.telViewUpTo recPars def.defType
      recTy <- translateTeleBindsToPi tel (pure RU)
      let fieldTel = snd $ Agda.splitTelescopeAt recPars recTel
      recBody <- translateTeleBindsToLam tel $ buildSigmaChain id recFields fieldTel
      pure [DLet Nothing qname recTy recBody]

translateConDef :: QName -> Agda.Definition -> Agda.TCM [Decl]
translateConDef qname def = do
  let Agda.Constructor {..} = def.theDef

  let buildPairChain pairs = \cases
        [n] -> do
          let x = fromString $ Agda.prettyShow $ Agda.qnameName $ Internal.unDom n
          pairs (RVar (Unqual x))
        (n : ns) -> do
          let x = fromString $ Agda.prettyShow $ Agda.qnameName $ Internal.unDom n
          buildPairChain (pairs . RPair (RVar (Unqual x))) ns
        _ -> __IMPOSSIBLE__

  recDef <- Agda.getConstInfo conData
  case recDef.theDef of
    Agda.Record {..}
      | Agda.theEtaEquality recEtaEquality' == Agda.YesEta && not (null recFields) -> do
          Agda.TelV parTel _ <- Agda.telViewUpTo recPars def.defType
          let fieldTel = snd $ Agda.splitTelescopeAt recPars recTel
          ctorTy <- translateType def.defType
          ctorBody <-
            translateTeleBindsToLam parTel $
              translateTeleBindsToLam fieldTel $
                pure (buildPairChain id recFields)
          pure [DLet Nothing qname ctorTy ctorBody]
    _ -> pure <$> translateIntoAxiom qname def.defType

translateFunDef :: QName -> Agda.Definition -> Agda.TCM [Decl]
translateFunDef qname def = do
  let Agda.Function {..} = def.theDef

  let buildProjChain snds = \cases
        [_] -> snds (RVar "r")
        (n : ns) ->
          if Internal.unDom n == def.defName
            then snds (RFst (RVar "r"))
            else buildProjChain (snds . RSnd) ns
        _ -> __IMPOSSIBLE__

  -- let checkNoLocalDefs = do
  --       defs <- Agda.curDefs @Agda.TCM
  --       pure $!
  --         null $
  --           takeWhile (Agda.isAnonymousModuleName . Agda.qnameModule) $
  --             dropWhile (<= def.defName) $
  --               map fst $
  --                 Agda.sortDefs defs

  case funProjection of
    Right proj
      | Just r <- Agda.projProper proj -> do
          recDef <- Agda.getConstInfo r
          case recDef.theDef of
            Agda.Record {..}
              | Agda.theEtaEquality recEtaEquality' == Agda.YesEta && not (null recFields) -> do
                  Agda.TelV parTel _ <- Agda.telViewUpTo recPars def.defType
                  projTy <- translateType def.defType
                  projBody <-
                    translateTeleBindsToLam parTel $
                      pure (RLam "r" $ buildProjChain id recFields)
                  pure [DLet Nothing qname projTy projBody]
            _ -> pure <$> translateIntoAxiom qname def.defType
    _ ->
      -- checkNoLocalDefs >>= \case
      --   False -> pure <$> translateIntoAxiom qname def.defType
      --   True -> case funClauses of
      -- case funClauses of
      --   [Internal.Clause {..}] -> do
      --     res <- Agda.addContext (Agda.KeepNames clauseTel) do
      --       translatePatternArgs def.defType namedClausePats >>= \case
      --         Nothing -> pure Nothing
      --         Just (ty, lams) -> do
      --           body <- translateTerm ty $ fromMaybe __IMPOSSIBLE__ clauseBody
      --           let body' = lams body
      --           pure $ Just body'
      --     case res of
      --       Nothing -> pure <$> translateIntoAxiom qname def.defType
      --       Just body -> do
      --         ty <- translateType def.defType
      --         pure [DLet Nothing qname ty body]
      -- _ -> pure <$> translateIntoAxiom qname def.defType
      pure <$> translateIntoAxiom qname def.defType

translatePatternArgs :: Internal.Type -> Internal.NAPs -> Agda.TCM (Maybe (Internal.Type, Raw -> Raw))
translatePatternArgs ty naps = do
  (ty, args) <-
    translateArgs' ty $
      map Agda.unArg $
        fromMaybe __IMPOSSIBLE__ $
          Internal.allApplyElims $
            Internal.patternsToElims naps

  let go lams = \case
        [] -> pure $ Just (ty, lams)
        RVar (Unqual n) : ns -> go (lams . RLam n) ns
        RVar (Qual {}) : _ -> __IMPOSSIBLE__
        _ -> pure Nothing

  go id args

--------------------------------------------------------------------------------

-- -- | Translate a simple definition (single clause, all VarP).
-- translateSimpleDef ::
--   QName -> Agda.Definition -> Agda.FunctionData -> Agda.TCM [Decl]
-- translateSimpleDef qname def fd = do
--   ty <- translateType def.defType
--   let cl = head fd._funClauses
--       tels = Internal.telToList cl.clauseTel
--   lvlFlags <- forM tels \e -> Agda.isLevelType (snd (Internal.unDom e))
--   body <- case cl.clauseBody of
--     Nothing -> pure (RVar (Unqual (Name "_")))
--     Just t -> Agda.addContext cl.clauseTel do
--       t' <- Agda.reduce t
--       goType t'
--   let varNames =
--         [ Name (T.pack (fst (Internal.unDom e)))
--         | (e, isLvl) <- zip tels lvlFlags,
--           not isLvl
--         ]
--       fullBody = foldr RLam body varNames
--   pure [DLet Nothing qname ty fullBody]

--------------------------------------------------------------------------------
-- Type alias predicates

-- isSimpleDef :: Agda.FunctionData -> Bool
-- isSimpleDef fd = case fd._funClauses of
--   [cl] | all isVarPat cl.namedClausePats -> True
--   _ -> False
--   where
--     isVarPat :: Agda.NamedArg Internal.DeBruijnPattern -> Bool
--     isVarPat p = case Agda.namedArg p of
--       Internal.VarP {} -> True
--       _ -> False

--------------------------------------------------------------------------------
-- Name translation helpers

translateModuleName :: Internal.ModuleName -> ModuleName
translateModuleName m =
  ModuleName $
    T.intercalate "." $
      map (T.pack . Concrete.nameToRawName . Internal.nameConcrete) $
        Internal.mnameToList m

translateTopLevelModuleName :: Agda.TopLevelModuleName -> ModuleName
translateTopLevelModuleName m =
  ModuleName $ T.intercalate "." $ toList m.moduleNameParts

translateQName :: Internal.QName -> QName
translateQName = translateCQName . Internal.qnameToConcrete

translateCQName :: Concrete.QName -> QName
translateCQName cqn =
  case splitCQName cqn of
    ([], n) -> Unqual (translateName n)
    (parts, n) ->
      Qual
        (ModuleName $ T.intercalate "." $ map (T.pack . Concrete.nameToRawName) parts)
        (translateName n)

splitCQName :: Concrete.QName -> ([Concrete.Name], Concrete.Name)
splitCQName (Concrete.QName n) = ([], n)
splitCQName (Concrete.Qual n rest) =
  let (parts, final) = splitCQName rest
   in (n : parts, final)

translateName :: Concrete.Name -> Name
translateName = \case
  n@(Concrete.Name {}) -> Name $ T.pack $ Concrete.nameToRawName n
  Concrete.NoName {} -> error "translateName: unexpected NoName"

translateDBVar :: Agda.Nat -> Agda.TCM Name
translateDBVar x = do
  n <- Agda.ceName <$> Agda.lookupBV x
  pure $ Name $ T.pack $ Agda.prettyShow $ Agda.nameConcrete n

--------------------------------------------------------------------------------
-- Utils

translateError :: (HasCallStack, Agda.MonadTCError m) => String -> m a
translateError msg = Agda.typeError $ Agda.CustomBackendError "dependent-type-search" (Agda.text msg)
