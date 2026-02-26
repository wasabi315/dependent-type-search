module TypeSearch.Translate (translateLibrary) where

import Agda.Compiler.Backend qualified as Agda
import Agda.Compiler.Common qualified as Agda
import Agda.Interaction.FindFile qualified as Agda
import Agda.Interaction.Imports qualified as Agda
import Agda.Interaction.Library qualified as Agda
import Agda.Interaction.Options qualified as Agda
import Agda.Syntax.Common qualified as Agda
import Agda.Syntax.Common.Pretty qualified as Agda
import Agda.Syntax.Concrete qualified as Concrete
import Agda.Syntax.Internal qualified as Internal
import Agda.Syntax.Internal.Pattern qualified as Internal
import Agda.Syntax.Literal qualified as Agda
import Agda.Syntax.Position qualified as Agda
import Agda.Syntax.Scope.Base qualified as Agda
import Agda.TypeChecking.Datatypes qualified as Agda
import Agda.TypeChecking.Level qualified as Agda
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
import Agda.Utils.Monad qualified as Agda
import Control.Monad (forM, forM_, when)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.IO.Class (liftIO)
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
-- Types

type M = Agda.TCM

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

--------------------------------------------------------------------------------
-- Module translation

translateModule :: Agda.TopLevelModuleName -> Agda.Source -> M Module
translateModule m src = do
  mi <- Agda.getNonMainModuleInfo m (Just src)
  let isInfectiveWarning Agda.InfectiveImport {} = True
      isInfectiveWarning _ = False
      warns = filter (not . isInfectiveWarning . Agda.tcWarning) $ Set.toAscList $ mi.miWarnings
  Agda.tcWarningsToError warns
  translateInterface mi.miInterface

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

translateInterface :: Agda.Interface -> M Module
translateInterface intf = do
  Agda.setInterface intf
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
  pure Module {name = modName, imports, decls}

--------------------------------------------------------------------------------
-- Definition translation

translateDefinition :: QName -> Agda.Definition -> M [Decl]
translateDefinition qname def = do
  case def.theDef of
    Agda.AxiomDefn {} -> pure <$> translateToAxiom qname def.defType
    Agda.AbstractDefn {} -> pure <$> translateToAxiom qname def.defType
    Agda.FunctionDefn {} -> translateFunDef qname def
    Agda.DatatypeDefn {} -> pure <$> translateToAxiom qname def.defType
    Agda.RecordDefn {} -> translateRecordDef qname def
    Agda.ConstructorDefn {} -> translateConDef qname def
    Agda.PrimitiveDefn {} -> pure <$> translateToAxiom qname def.defType
    Agda.DataOrRecSigDefn {} -> pure []
    Agda.GeneralizableVar {} -> pure []
    Agda.PrimitiveSortDefn {} -> pure []

translateToAxiom :: QName -> Internal.Type -> M Decl
translateToAxiom x ty = DAxiom Nothing x <$> translateType ty

--------------------------------------------------------------------------------
-- Internal term/type → Raw

translateType :: Internal.Type -> M Raw
translateType ty = translateTerm (Agda.sort ty._getSort) ty.unEl

translateTerm :: Internal.Type -> Internal.Term -> M Raw
translateTerm ty v = do
  v <- Agda.instantiate v
  Agda.reduceProjectionLike v >>= \case
    Internal.Sort _ -> pure RU
    Internal.Pi a b -> do
      let compileB = Agda.underAbstraction a b translateType
      translateDomType b.absName a >>= \case
        Nothing -> compileB
        Just (x, a) -> RPi x a <$> compileB
    Internal.Var i es -> do
      ty <- Agda.typeOfBV i
      translateSpined (translateVar i ty) (Internal.Var i) ty es
    Internal.Def f es -> do
      ty <- Agda.defType <$> Agda.getConstInfo f
      translateSpined (translateDef f ty) (Internal.Def f) ty es
    Internal.Con ch ci es -> do
      Just ((_, _, pars), ty) <- Agda.getConType ch ty
      translateSpined (translateCon ch ci ty pars) (Internal.Con ch ci) ty es
    Internal.Lam v b -> translateLam ty v b
    Internal.Lit x -> translateLit x
    Internal.Level {} ->
      translateError "Bad term: Level"
    Internal.MetaV {} ->
      translateError "Bad term: MetaV"
    Internal.DontCare {} ->
      translateError "Bad term: DontCare"
    Internal.Dummy {} ->
      translateError "Bad term: Dummy"

translateVar :: Int -> Internal.Type -> [Internal.Term] -> M Raw
translateVar i ty args = do
  name <- translateDBVar i
  translateApp (RVar $ Unqual name) ty args

translateDef :: Internal.QName -> Internal.Type -> [Internal.Term] -> M Raw
translateDef f ty args = do
  let name = translateQName f
  translateApp (RVar name) ty args

translateCon :: Internal.ConHead -> Internal.ConInfo -> Internal.Type -> Internal.Args -> [Internal.Term] -> M Raw
translateCon ch i ty pars args = do
  let c = ch.conName
  conDef <- Agda.getConstInfo c
  let Agda.Constructor {..} = conDef.theDef
  if Agda.defCopy conDef
    then translateCon conSrcCon i ty pars args
    else do
      let name = translateQName c
      dataDef <- Agda.getConstInfo conData
      -- For making parameters explicit
      -- e.g) Agda.Builtin.List._∷_ x xs -> Agda.Builtin.List._∷_ A x xs
      t <- translateApp (RVar name) dataDef.defType $ map Agda.unArg pars
      translateApp t ty args

translateSpined ::
  ([Internal.Term] -> M Raw) ->
  (Internal.Elims -> Internal.Term) ->
  Internal.Type ->
  Internal.Elims ->
  M Raw
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
  Internal.QName ->
  Internal.Type ->
  Internal.Term ->
  Internal.Type ->
  [Internal.Term] ->
  M Raw
translateProj q tty t ty args = do
  let name = translateQName q
  arg <- translateTerm tty t
  translateApp (RVar name `RApp` arg) ty args

translateApp :: Raw -> Internal.Type -> [Internal.Term] -> M Raw
translateApp f ty args = do
  args <- translateArgs ty args
  pure $! foldl' RApp f args

translateArgs :: Internal.Type -> [Internal.Term] -> M [Raw]
translateArgs ty args = snd <$> translateArgs' ty args

translateArgs' :: Internal.Type -> [Internal.Term] -> M (Internal.Type, [Raw])
translateArgs' ty = \case
  [] -> pure (ty, [])
  (x : xs) -> do
    (a, b) <- Agda.mustBePi ty
    let rest = translateArgs' (Agda.absApp b x) xs
    Agda.ifM
      (isErasable a.unDom)
      do rest
      do
        x <- translateTerm a.unDom x
        (ty, xs) <- rest
        pure (ty, x : xs)

translateLam :: Internal.Type -> Agda.ArgInfo -> Internal.Abs Internal.Term -> M Raw
translateLam ty _argi abs = do
  (dom, cod) <- Agda.mustBePi ty
  Agda.ifM
    (isErasable dom.unDom)
    do Agda.addContext dom $ translateTerm (Agda.absBody cod) (Agda.absBody abs)
    do
      let varName = abs.absName
          ctxElt = (varName,) <$> dom
      fmap (RLam (fromString varName)) $
        Agda.addContext ctxElt $
          translateTerm (Agda.absBody cod) (Agda.absBody abs)

translateDomType :: Agda.ArgName -> Internal.Dom Internal.Type -> M (Maybe (Name, Raw))
translateDomType x a =
  Agda.ifM
    (isErasable a.unDom)
    do pure Nothing
    do
      a <- translateType a.unDom
      pure $ Just (fromString x, a)

isErasable :: Internal.Type -> M Bool
isErasable a = do
  Agda.TelV tel b <- Agda.telView a
  Agda.addContext tel $
    Agda.orM
      [ Agda.isLevelType b,
        isJust <$> Agda.isSizeType b
      ]

translateTeleBindsToPi :: Internal.Telescope -> M Raw -> M Raw
translateTeleBindsToPi tel body = go id tel
  where
    go pis = \case
      Internal.EmptyTel -> pis <$> body
      Internal.ExtendTel a tel ->
        translateDomType tel.absName a >>= \case
          Nothing -> Agda.underAbstraction a tel $ go pis
          Just (x, a') -> do
            Agda.underAbstraction a tel $ go (pis . RPi x a')

translateTeleBindsToLam :: Internal.Telescope -> M Raw -> M Raw
translateTeleBindsToLam tel body = go id tel
  where
    go lams = \case
      Internal.EmptyTel -> lams <$> body
      Internal.ExtendTel a tel ->
        Agda.ifM
          (isErasable a.unDom)
          do Agda.underAbstraction a tel $ go lams
          do
            let x = fromString tel.absName
            Agda.underAbstraction a tel $ go (lams . RLam x)

translateLit :: Agda.Literal -> M Raw
translateLit = \case
  Agda.LitNat n -> do
    zero <- translateQName <$> Agda.getBuiltinName_ Agda.BuiltinZero
    suc <- translateQName <$> Agda.getBuiltinName_ Agda.BuiltinSuc
    pure $ applyN (fromInteger n) (RVar suc `RApp`) (RVar zero)
  _ -> translateError "unsupported literal"

--------------------------------------------------------------------------------
-- Non-empty record with eta-equality → Σ chain

isSigmaTranslatable :: Agda.Definition -> Bool
isSigmaTranslatable def = case def.theDef of
  Agda.Record {..} ->
    Agda.theEtaEquality recEtaEquality' == Agda.YesEta && not (null recFields)
  _ -> False

translateToSigma :: QName -> Agda.Definition -> M [Decl]
translateToSigma qname def = do
  let Agda.Record {..} = def.theDef

  -- FIXME: Erase erasable fields
  let buildSigmaChain sigmas = \cases
        [_] (Internal.ExtendTel a _) -> sigmas <$> translateType a.unDom
        (n : ns) (Internal.ExtendTel a tel) -> do
          let x = fromString $ Agda.prettyShow n.unDom.qnameName
          a' <- translateType a.unDom
          Agda.underAbstraction a tel $ buildSigmaChain (sigmas . RSigma x a') ns
        _ _ -> __IMPOSSIBLE__

  Agda.TelV tel _ <- Agda.telViewUpTo recPars def.defType
  recTy <- translateTeleBindsToPi tel (pure RU)
  let fieldTel = snd $ Agda.splitTelescopeAt recPars recTel
  recBody <- translateTeleBindsToLam tel $ buildSigmaChain id recFields fieldTel
  pure [DLet Nothing qname recTy recBody]

translateToPairs :: QName -> Agda.Definition -> Agda.Definition -> M [Decl]
translateToPairs qname recDef conDef = do
  let Agda.Record {..} = recDef.theDef
      Agda.Constructor {..} = conDef.theDef

  let buildPairChain pairs = \cases
        [n] -> do
          let x = fromString $ Agda.prettyShow n.unDom.qnameName
          pairs (RVar (Unqual x))
        (n : ns) -> do
          let x = fromString $ Agda.prettyShow n.unDom.qnameName
          buildPairChain (pairs . RPair (RVar (Unqual x))) ns
        _ -> __IMPOSSIBLE__

  Agda.TelV parTel _ <- Agda.telViewUpTo recPars conDef.defType
  let fieldTel = snd $ Agda.splitTelescopeAt recPars recTel
  ctorTy <- translateType conDef.defType
  ctorBody <-
    translateTeleBindsToLam parTel $
      translateTeleBindsToLam fieldTel $
        pure (buildPairChain id recFields)
  pure [DLet Nothing qname ctorTy ctorBody]

translateToFstSnd :: QName -> Agda.Definition -> Agda.Definition -> M [Decl]
translateToFstSnd qname recDef projDef = do
  let Agda.Record {..} = recDef.theDef
      Agda.Function {..} = projDef.theDef

  let buildFstSndChain snds = \cases
        [_] -> snds (RVar "r")
        (n : ns) ->
          if n.unDom == projDef.defName
            then snds (RFst (RVar "r"))
            else buildFstSndChain (snds . RSnd) ns
        _ -> __IMPOSSIBLE__

  Agda.TelV parTel _ <- Agda.telViewUpTo recPars projDef.defType
  projTy <- translateType projDef.defType
  projBody <-
    translateTeleBindsToLam parTel $
      pure (RLam "r" $ buildFstSndChain id recFields)
  pure [DLet Nothing qname projTy projBody]

--------------------------------------------------------------------------------
-- Translate type-alias-like into let
--   * The return type *can* be Set
--   * No where clause
--   * No pattern matching

isTypeAliasLike :: Agda.Definition -> M Bool
isTypeAliasLike def =
  Agda.andM
    [ canEndInSort def.defType,
      hasNoLocalDefs def,
      pure $ isNonPatternMatching def
    ]

canEndInSort :: Internal.Type -> M Bool
canEndInSort t = do
  Agda.TelV tel b <- Agda.telView t
  Agda.addContext tel do
    b <- Agda.reduce b
    case b.unEl of
      Internal.Sort {} -> pure True
      Internal.Var {} -> pure True
      _ -> pure False

hasNoLocalDefs :: Agda.Definition -> M Bool
hasNoLocalDefs def = do
  defs <- Agda.curDefs
  let locals =
        takeWhile (Agda.isAnonymousModuleName . Agda.qnameModule) $
          dropWhile (<= def.defName) $
            map fst $
              Agda.sortDefs defs
  pure $! null locals

isNonPatternMatching :: Agda.Definition -> Bool
isNonPatternMatching def = do
  let Agda.Function {..} = def.theDef
  case funClauses of
    [cl] -> flip all cl.namedClausePats \nap ->
      case nap.unArg.namedThing of
        Internal.VarP {} -> isJust cl.clauseBody
        _ -> False
    _ -> False

-- FIXME: translate
offendingDefs :: [String]
offendingDefs =
  [ -- mustBePi
    "Algebra.Consequences.Setoid.subst+comm⇒sym"
  ]

translateTypeAliasLike :: QName -> Agda.Definition -> M [Decl]
translateTypeAliasLike qname def = do
  when (show qname `elem` offendingDefs) do
    translateError "skip for now"
  let Agda.Function {..} = def.theDef
      [Internal.Clause {..}] = funClauses
  funTy <- translateType def.defType
  Agda.addContext (Agda.KeepNames clauseTel) do
    (bodyTy, argLams) <- translatePatternArgs def.defType namedClausePats
    fun <- argLams <$> translateTerm bodyTy (fromMaybe __IMPOSSIBLE__ clauseBody)
    pure [DLet Nothing qname funTy fun]

translatePatternArgs :: Internal.Type -> Internal.NAPs -> M (Internal.Type, Raw -> Raw)
translatePatternArgs ty naps = do
  (ty, args) <-
    translateArgs' ty $
      map Agda.unArg $
        fromMaybe __IMPOSSIBLE__ $
          Internal.allApplyElims $
            Internal.patternsToElims naps

  let varToLam = \case
        RVar (Unqual n) -> RLam n
        _ -> __IMPOSSIBLE__

  pure (ty, foldr ((.) . varToLam) id args)

--------------------------------------------------------------------------------

translateRecordDef :: QName -> Agda.Definition -> M [Decl]
translateRecordDef qname def = do
  if isSigmaTranslatable def
    then translateToSigma qname def
    else pure <$> translateToAxiom qname def.defType

translateConDef :: QName -> Agda.Definition -> M [Decl]
translateConDef qname def = do
  let Agda.Constructor {..} = def.theDef
  recDef <- Agda.getConstInfo conData
  if isSigmaTranslatable recDef
    then translateToPairs qname recDef def
    else pure <$> translateToAxiom qname def.defType

translateFunDef :: QName -> Agda.Definition -> M [Decl]
translateFunDef qname def = do
  let Agda.Function {..} = def.theDef

  Agda.inTopContext $
    Agda.withCurrentModule def.defName.qnameModule $
      case funProjection of
        Right (Agda.projProper -> Just r) -> do
          recDef <- Agda.getConstInfo r
          if isSigmaTranslatable recDef
            then translateToFstSnd qname recDef def
            else pure <$> translateToAxiom qname def.defType
        _ ->
          Agda.ifM
            (isTypeAliasLike def)
            do translateTypeAliasLike qname def
            do pure <$> translateToAxiom qname def.defType

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

translateDBVar :: Agda.Nat -> M Name
translateDBVar x = do
  n <- Agda.ceName <$> Agda.lookupBV x
  pure $ Name $ T.pack $ Agda.prettyShow $ Agda.nameConcrete n

--------------------------------------------------------------------------------
-- Utils

translateError :: (HasCallStack, Agda.MonadTCError m) => String -> m a
translateError msg = Agda.typeError $ Agda.CustomBackendError "dependent-type-search" (fromString msg)
