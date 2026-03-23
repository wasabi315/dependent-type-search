{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module TypeSearch.Database.Index where

import Agda.Compiler.Backend hiding (Args, initEnv)
import Agda.Compiler.Common
import Agda.Interaction.FindFile
import Agda.Interaction.Imports
import Agda.Interaction.Library
import Agda.Interaction.Options
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Concrete qualified as Concrete
import Agda.Syntax.Internal hiding (arity, termSize)
import Agda.Syntax.Internal.Defs
import Agda.Syntax.Literal
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad (getCurrentScope)
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Level
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.ProjectionLike
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute as Agda
import Agda.TypeChecking.Telescope
import Agda.Utils.CallStack (HasCallStack)
import Agda.Utils.FileName
import Agda.Utils.Function
import Agda.Utils.IO.Directory
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Monad
import Control.Monad.Except (throwError)
import Control.Monad.Reader
import Data.Coerce
import Data.HashSet qualified as HS
import Data.IntMap qualified as IM
import Data.List (sort)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.String
import Data.Text qualified as T
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Types
import System.Directory
import System.FilePath.Find qualified as Find
import TypeSearch.Common qualified as TS
import TypeSearch.Database.Common qualified as TS
import TypeSearch.Term qualified as TS

--------------------------------------------------------------------------------
-- Types

data IndexConfig = IndexConfig
  { -- | Maximum Raw node count for a let-body; larger bodies fall back to DAxiom.
    maxLetSize :: Int,
    -- | Path to Agda library.
    libraryDirectory :: FilePath,
    -- | Connection to database.
    databaseConnection :: Connection
  }

data IndexEnv = IndexEnv
  { maxLetSize :: Int,
    -- | Context size after erasure
    contextSizeAfterErasure :: Int,
    -- | De Bruijn level to De Bruijn level after erasure
    renaming :: IM.IntMap Int
  }

type M = ReaderT IndexEnv TCM

initEnv :: IndexConfig -> IndexEnv
initEnv IndexConfig {..} = IndexEnv maxLetSize 0 mempty

addContextAndRenaming :: (AddContext (name, Dom Type)) => (name, Dom Type) -> M a -> M a
addContextAndRenaming ctxElt m = do
  ctxSize <- getContextSize
  local
    ( \env ->
        env
          { contextSizeAfterErasure = env.contextSizeAfterErasure + 1,
            renaming = IM.insert ctxSize env.contextSizeAfterErasure env.renaming
          }
    )
    $ addContext ctxElt m

realName :: ArgName -> String
realName s = if isNoName s then "x" else argNameToString s

translateError :: (HasCallStack, MonadTCError m) => m Doc -> m a
translateError msg = typeError . CustomBackendError "dependent-type-search" =<< msg

--------------------------------------------------------------------------------

data Item = Item
  { name :: TS.QName,
    signature :: TS.Term,
    body :: Maybe TS.Term,
    occurrence :: Maybe [Bool],
    feature :: (HS.HashSet TS.Name, HS.HashSet TS.Name, TS.ReturnTypeHead, HS.HashSet TS.Name, TS.Polymorphic, TS.Arity),
    returnSortBody :: Maybe TS.ReturnSort,
    canonishBody :: Maybe (HS.HashSet TS.Name)
  }

--------------------------------------------------------------------------------
-- Compute features

feature :: Type -> M (HS.HashSet TS.Name, HS.HashSet TS.Name, TS.ReturnTypeHead, HS.HashSet TS.Name, TS.Polymorphic, TS.Arity)
feature t = do
  cs <- getDefNames =<< normalise t
  ncs <- (`HS.difference` cs) <$> getDefNames t
  (rt, rcs) <- returnTypeFeatures t
  pl <- isPolymorphic t
  ar <- arity t
  pure (ncs, cs, rt, rcs, pl, ar)

returnTypeFeatures :: Type -> M (TS.ReturnTypeHead, HS.HashSet TS.Name)
returnTypeFeatures t = do
  TelV tel b <- telView t
  addContext tel do
    b <- normalise b
    canons <- getDefNames b
    case b.unEl of
      Sort {} -> pure (TS.RHSort, canons)
      Var {} -> pure (TS.RHVar, canons)
      Def f _ -> pure (TS.RHFormer (translateQName f).name, canons)
      _ -> pure (TS.RHOther, canons)

-- | Check if a given type may return Sort.
returnSort :: Type -> M TS.ReturnSort
returnSort t = do
  TelV tel b <- telView t
  addContext tel do
    b <- reduce b
    case b.unEl of
      Sort {} -> pure TS.YesReturnSort
      Var i _ -> do
        ty <- typeOfBV i
        TelV _ b <- telView ty
        pure $ case b.unEl of
          Sort {} -> TS.MayReturnSort
          _ -> TS.NoReturnSort
      _ -> pure TS.NoReturnSort

returnSortBody :: Term -> M (Maybe TS.ReturnSort)
returnSortBody = \case
  Sort {} -> pure (Just TS.YesReturnSort)
  Pi a b -> underAbstraction a b (fmap Just . returnSort)
  Lam _ t -> underAbstraction_ t returnSortBody
  Def {} -> pure (Just TS.NoReturnSort)
  _ -> pure Nothing

-- | Check if a given type is polymorphic.

-- FIXME: Look under records
isPolymorphic :: Type -> M TS.Polymorphic
isPolymorphic t = ifNotPiType t (\_ -> pure TS.NoPolymorphic) \a rest -> do
  TelV _ b <- telView a.unDom
  case b.unEl of
    Sort {} -> pure TS.YesPolymorphic
    _ -> underAbstraction a rest isPolymorphic

arity :: Type -> M TS.Arity
arity = go (0 :: Int)
  where
    go acc t =
      ifPiType
        t
        ( \dom rest -> do
            dom <- reduce dom
            case dom.unDom.unEl of
              Var i _ -> do
                ty <- typeOfBV i
                TelV _ b <- telView ty
                case b.unEl of
                  Sort {} -> pure TS.InfArity
                  _ -> underAbstraction dom rest (go (acc + 1))
              _ -> underAbstraction dom rest (go (acc + 1))
        )
        ( \cod -> do
            cod <- reduce cod
            case cod.unEl of
              Var i _ -> do
                ty <- typeOfBV i
                TelV _ b <- telView ty
                case b.unEl of
                  Sort {} -> pure TS.InfArity
                  _ -> pure (TS.Arity acc)
              _ -> pure (TS.Arity acc)
        )

--------------------------------------------------------------------------------
-- Entrypoint

checkModuleName' :: TopLevelModuleName' Range -> SourceFile -> TCM ()
checkModuleName' m f =
  setCurrentRange m $ checkModuleName m f Nothing

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
    let env = initEnv config
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
            liftIO $ saveModule config.databaseConnection mod'

saveModule :: Connection -> [Item] -> IO ()
saveModule conn items = do
  let values = flip map items \(Item n a t occ (ncs, cs, return_type_head, rcs, polymorphic, arity) return_sort_body bcs) -> do
        let name_qual = TS.DbQName n
            name_unqual = TS.DbName n.name
            modul = TS.DbModuleName n.moduleName
            sig = TS.DbTerm a
            body = TS.DbTerm <$> t
            occurrence = PGArray <$> occ
            noncanonish = PGArray $ coerce $ HS.toList ncs
            canonish = PGArray $ coerce $ HS.toList cs
            body_canonish = PGArray . coerce . HS.toList <$> bcs
            return_type_canonish = PGArray $ coerce $ HS.toList rcs
        TS.DbItem {..}
  TS.saveManyItems conn values

--------------------------------------------------------------------------------
-- Module translation

translateInterface :: Interface -> M [Item]
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

setCurrentRangeQ :: QName -> M a -> M a
setCurrentRangeQ = setCurrentRange . nameBindingSite . qnameName

translateDefinition :: TS.QName -> Definition -> M [Item]
translateDefinition qname def = setCurrentRangeQ def.defName do
  ifM
    (isErasable def.defType)
    do pure []
    case def.theDef of
      AxiomDefn {} -> pure <$> translateToAxiom qname def.defType (Just TS.NoReturnSort)
      AbstractDefn {} -> pure <$> translateToAxiom qname def.defType (Just TS.NoReturnSort)
      FunctionDefn {} -> translateFunDef qname def
      DatatypeDefn {} -> pure <$> translateToAxiom qname def.defType (Just TS.NoReturnSort)
      RecordDefn {} -> pure <$> translateToAxiom qname def.defType (Just TS.NoReturnSort)
      ConstructorDefn {} -> pure <$> translateToAxiom qname def.defType (Just TS.NoReturnSort)
      PrimitiveDefn {} -> pure <$> translateToAxiom qname def.defType (Just TS.NoReturnSort)
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

translateToAxiom :: TS.QName -> Type -> Maybe TS.ReturnSort -> M Item
translateToAxiom x ty retSortBody = do
  feat <- feature ty
  ty <- translateType ty
  pure $! Item x ty Nothing Nothing feat retSortBody Nothing

translateFunDef :: TS.QName -> Definition -> M [Item]
translateFunDef qname def = do
  ifM
    (isTypeAliasLike def)
    do translateTypeAliasLike qname def
    do pure <$> translateToAxiom qname def.defType (Just TS.NoReturnSort)

--------------------------------------------------------------------------------
-- Internal term/type → Term

translateType :: Type -> M TS.Term
translateType ty = translateTerm (Agda.sort ty._getSort) ty.unEl

translateTerm :: Type -> Term -> M TS.Term
translateTerm ty v = do
  v <- instantiate v

  let bad s t =
        translateError $
          vcat
            [ "cannot compile" <+> text (s ++ ":"),
              nest 2 $ prettyTCM t
            ]

  reduceProjectionLike v >>= \case
    Sort _ -> pure TS.U
    Pi a b -> do
      translateDomType a >>= \case
        Nothing -> underAbstraction a b translateType
        Just a' -> do
          let name = if isBinderUsed b then realName b.absName else "_"
          addContextAndRenaming (KeepNames name, a) $
            TS.Pi (fromString name) a' <$> translateType (absBody b)
    Var i es -> do
      ty <- typeOfBV i
      translateSpined (translateVar i ty) (Var i) ty es
    Def f es -> maybeUnfoldCopy f es (translateTerm ty) \f es -> do
      def <- getConstInfo f
      let ty = def.defType
          f' = def.defName
      translateSpined (translateDef f' ty) (Def f') ty es
    Con ch ci es -> do
      Just ((_, _, pars), ty) <- getConType ch ty
      translateSpined (translateCon ch ci ty pars) (Con ch ci) ty es
    Lam v b -> translateLam ty v b
    Lit x -> translateLit x
    v@MetaV {} -> bad "unsolved metavariable" v
    v@DontCare {} -> bad "irrelevant term" v
    v@Dummy {} -> bad "dummy term" v
    Level {} -> __IMPOSSIBLE__

translateVar :: Int -> Type -> [Term] -> M TS.Term
translateVar i ty args = do
  i <- translateDBVar i
  translateApp (TS.Var i) ty args

translateDef :: QName -> Type -> [Term] -> M TS.Term
translateDef f ty args = do
  let name = translateQName f
  translateApp (TS.Top name) ty args

translateCon :: ConHead -> ConInfo -> Type -> Args -> [Term] -> M TS.Term
translateCon ch i ty pars args = do
  let c = ch.conName
  conDef <- getConstInfo c
  let Constructor {..} = conDef.theDef
  if defCopy conDef
    then translateCon conSrcCon i ty pars args
    else do
      let name = translateQName conSrcCon.conName
      dataDef <- getConstInfo conData
      -- For making parameters explicit
      -- e.g) Builtin.List._∷_ x xs -> Builtin.List._∷_ A x xs
      t <- translateApp (TS.Top name) dataDef.defType $ map unArg pars
      translateApp t ty args

translateSpined ::
  ([Term] -> M TS.Term) ->
  (Elims -> Term) ->
  Type ->
  Elims ->
  M TS.Term
translateSpined c tm ty = \case
  [] -> c []
  e@(Proj o q) : es -> do
    let t = tm []
    ty' <- shouldBeProjectible t ty o q
    translateSpined (translateProj q ty t ty') (tm . (e :)) ty' es
  e@(Apply (unArg -> x)) : es -> do
    (_, b) <- mustBePi ty
    translateSpined (c . (x :)) (tm . (e :)) (absApp b x) es
  e@IApply {} : _ ->
    translateError $
      vcat ["cannot compile IApply:", nest 2 $ prettyTCM e]

translateProj ::
  QName ->
  Type ->
  Term ->
  Type ->
  [Term] ->
  M TS.Term
translateProj q tty t ty args = do
  let name = translateQName q
  arg <- translateTerm tty t
  translateApp (TS.Top name `TS.App` arg) ty args

translateApp :: TS.Term -> Type -> [Term] -> M TS.Term
translateApp f ty args = do
  args <- translateArgs ty args
  pure $! foldl' TS.App f args

translateArgs :: Type -> [Term] -> M [TS.Term]
translateArgs ty args = snd <$> translateArgs' ty args

translateArgs' :: Type -> [Term] -> M (Type, [TS.Term])
translateArgs' ty = \case
  [] -> pure (ty, [])
  (x : xs) -> do
    (a, b) <- mustBePi ty
    let rest = translateArgs' (absApp b x) xs
    ifM
      (isErasable a.unDom)
      do rest
      do
        x <- translateTerm a.unDom x
        (ty, xs) <- rest
        pure (ty, x : xs)

translateLam :: Type -> ArgInfo -> Abs Term -> M TS.Term
translateLam ty _argi abs = do
  (dom, cod) <- mustBePi ty
  let name = realName abs.absName
      ctxElt = (KeepNames name, dom)
  ifM
    (isErasable dom.unDom)
    do addContext ctxElt $ translateTerm (absBody cod) (absBody abs)
    do
      addContextAndRenaming ctxElt $
        TS.Lam (fromString name) <$> translateTerm (absBody cod) (absBody abs)

translateDomType :: Dom Type -> M (Maybe TS.Term)
translateDomType a =
  ifM
    (isErasable a.unDom)
    do pure Nothing
    do
      a <- translateType a.unDom
      pure $ Just a

isErasable :: Type -> M Bool
isErasable a = do
  TelV tel b <- telView a
  addContext tel $
    orM
      [ isLevelType b,
        isJust <$> isSizeType b
      ]

translateLit :: Literal -> M TS.Term
translateLit = \case
  LitNat n -> do
    zero <- translateQName <$> getBuiltinName_ BuiltinZero
    suc <- translateQName <$> getBuiltinName_ BuiltinSuc
    pure $ iterate' n (TS.Top suc `TS.App`) (TS.Top zero)
  _ -> translateError "unsupported literal"

maybeUnfoldCopy :: QName -> Elims -> (Term -> M a) -> (QName -> Elims -> M a) -> M a
maybeUnfoldCopy f es onTerm onDef =
  reduceDefCopy f es >>= \case
    NoReduction () -> onDef f es
    YesReduction _ t -> onTerm t

--------------------------------------------------------------------------------
-- Translate type-alias-like into let
--   * The return type *can* be Set
--   * No where clause
--   * No pattern matching

isTypeAliasLike :: Definition -> M Bool
isTypeAliasLike def =
  andM
    [ (/= TS.NoReturnSort) <$> returnSort def.defType,
      hasNoLocalDefs def,
      pure $ isNonPatternMatching def,
      -- FIXME: translate projection-like
      isNotProjectionLike def
    ]

hasNoLocalDefs :: Definition -> M Bool
hasNoLocalDefs def = do
  defs <- curDefs
  let locals =
        takeWhile (isAnonymousModuleName . qnameModule) $
          dropWhile (<= def.defName) $
            map fst $
              sortDefs defs
  pure $! null locals

isNonPatternMatching :: Definition -> Bool
isNonPatternMatching def = do
  let Function {..} = def.theDef
  case funClauses of
    [cl] -> flip all cl.namedClausePats \nap ->
      case nap.unArg.namedThing of
        VarP {} -> isJust cl.clauseBody
        _ -> False
    _ -> False

isNotProjectionLike :: Definition -> M Bool
isNotProjectionLike def = do
  let Function {..} = def.theDef
  case funProjection of
    Left {} -> pure True
    Right {} -> do
      liftIO $ putStrLn $ "Found projection-like: " ++ prettyShow def.defName
      pure False

getOccs :: [Occurrence] -> Type -> M [Bool]
getOccs = \cases
  [] _ -> pure []
  (occ : occs) t -> do
    (a, b) <- mustBePi t
    ifM
      (isErasable a.unDom)
      (underAbstraction a b (getOccs occs))
      (((occ /= Unused) :) <$> underAbstraction a b (getOccs occs))

translateTypeAliasLike :: TS.QName -> Definition -> M [Item]
translateTypeAliasLike qname def = do
  let Function {..} = def.theDef
      [Clause {..}] = funClauses
  funTy <- translateType def.defType
  occ <- getOccs def.defArgOccurrences def.defType
  let occ' = if and occ then Nothing else Just occ
  fun <- translatePatternArgs def.defType namedClausePats \ty -> do
    clauseBody <- normalise (fromMaybe __IMPOSSIBLE__ clauseBody)
    translateTerm ty clauseBody
  feat <- feature def.defType
  addContext (KeepNames clauseTel) do
    clauseBody <- normalise (fromMaybe __IMPOSSIBLE__ clauseBody)
    retSortBody <- returnSortBody clauseBody
    canons <- getDefNames clauseBody
    maxSize <- asks \config -> config.maxLetSize
    if termSize fun <= maxSize
      then do
        pure [Item qname funTy (Just fun) occ' feat retSortBody (Just canons)]
      else pure [Item qname funTy Nothing Nothing feat (Just TS.NoReturnSort) Nothing]

termSize :: TS.Term -> Int
termSize = \case
  TS.Var {} -> 1
  TS.Top {} -> 1
  TS.U -> 1
  TS.Pi _ a b -> 1 + termSize a + termSize b
  TS.Lam _ t -> 1 + termSize t
  TS.App t u -> 1 + termSize t + termSize u
  TS.Sigma _ a b -> 1 + termSize a + termSize b
  TS.Pair t u -> 1 + termSize t + termSize u
  TS.Proj1 t -> 1 + termSize t
  TS.Proj2 t -> 1 + termSize t
  TS.Meta {} -> __IMPOSSIBLE__
  TS.AppPruning {} -> __IMPOSSIBLE__

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
  _ _ _ -> __IMPOSSIBLE__

--------------------------------------------------------------------------------
-- Name translation helpers

translateModuleName :: ModuleName -> TS.ModuleName
translateModuleName m =
  TS.ModuleName $
    T.intercalate "." $
      map (T.pack . Concrete.nameToRawName . nameConcrete) $
        filter (not . isNoName) $
          mnameToList m

translateTopLevelModuleName :: TopLevelModuleName -> TS.ModuleName
translateTopLevelModuleName =
  TS.ModuleName
    . T.intercalate "."
    . NonEmpty.toList
    . moduleNameParts

translateQName :: QName -> TS.QName
translateQName f = do
  let x = translateName $ nameConcrete $ qnameName f
      m = translateModuleName $ qnameModule f
  TS.QName m x

translateName :: Concrete.Name -> TS.Name
translateName = TS.Name . T.pack . Concrete.nameToRawName

translateDBVar :: Nat -> M TS.Index
translateDBVar agdaIx = do
  ctxSize <- getContextSize
  let lvl = ctxSize - agdaIx - 1
  join $ asks \env -> case IM.lookup lvl env.renaming of
    Nothing -> __IMPOSSIBLE__
    Just lvl' -> pure $! TS.Index (env.contextSizeAfterErasure - lvl' - 1)
