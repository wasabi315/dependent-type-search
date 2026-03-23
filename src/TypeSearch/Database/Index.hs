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
import Agda.Syntax.Internal hiding (arity, termSize)
import Agda.Syntax.Internal.Defs
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad (getCurrentScope)
import Agda.TypeChecking.Positivity.Occurrence
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Sort (ifIsSort)
import Agda.TypeChecking.Substitute as Agda
import Agda.TypeChecking.Telescope
import Agda.Utils.FileName
import Agda.Utils.IO.Directory
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Monad
import Control.Monad.Except (throwError)
import Control.Monad.Reader
import Data.Coerce
import Data.HashSet qualified as HS
import Data.List (sort)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.String
import Database.PostgreSQL.Simple
import Database.PostgreSQL.Simple.Types
import System.Directory
import System.FilePath.Find qualified as Find
import TypeSearch.Common qualified as TS
import TypeSearch.Database.Common qualified as TS
import TypeSearch.Database.Index.Common
import TypeSearch.Database.Index.Name
import TypeSearch.Database.Index.Term
import TypeSearch.Term qualified as TS

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
  ifIsSort b (\_ -> pure TS.YesPolymorphic) (underAbstraction a rest isPolymorphic)

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
