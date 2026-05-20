module TypeSearch.Translate.Module
  ( translateScope,
  )
where

import Agda.Compiler.Backend
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Scope.Base
import Data.DList qualified as DL
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as M
import TypeSearch.AgdaUtils
import TypeSearch.Core.Module qualified as TS
import TypeSearch.Prelude
import TypeSearch.Translate.Definition
import TypeSearch.Translate.Monad
import TypeSearch.Translate.Name

--------------------------------------------------------------------------------

translateScope :: ScopeInfo -> Transl TS.Module
translateScope scopeInfo = do
  definitions <- forMaybe (collectPublicNames scopeInfo) \(cname, aname) -> do
    def <- getConstInfo aname
    let name =
          translateConcreteQName
            (translateModuleName scopeInfo._scopeCurrent)
            cname
    translateDefinition name def
  let reexports =
        collectReexportNames scopeInfo
          <&> \(cname, aname) -> do
            let exportAs =
                  translateConcreteQName
                    (translateModuleName scopeInfo._scopeCurrent)
                    cname
                canonicalName = translateQName aname
            TS.Reexport {..}
  pure $! TS.Module {..}

collectPublicNames :: ScopeInfo -> [(C.QName, QName)]
collectPublicNames scopeInfo =
  DL.toList $ go id $ getScope scopeInfo._scopeCurrent
  where
    getScope m = scopeInfo._scopeModules M.! m

    go _ scope
      | scope.scopeDatatypeModule == Just IsDataModule = mempty
    go qual scope = names <> namesInChildren
      where
        names = do
          (cname, anames) <-
            DL.fromList $
              M.toList $
                namesInScope @AbstractName [PublicNS] scope
          aname <- DL.fromList $ NE.toList anames
          guard $ aname.anameKind /= PatternSynName
          pure (qual (C.QName cname), aname.anameName)

        namesInChildren = do
          (cmodName, amods) <-
            DL.fromList $
              M.toList $
                namesInScope @AbstractModule [PublicNS] scope
          amod <- DL.fromList $ NE.toList amods
          go (qual . C.Qual cmodName) (getScope amod.amodName)

collectReexportNames :: ScopeInfo -> [(C.QName, QName)]
collectReexportNames scopeInfo = do
  let scope = scopeInfo._scopeModules M.! scopeInfo._scopeCurrent
  guard $ scope.scopeDatatypeModule /= Just IsDataModule
  (cname, anames) <- M.toList $ namesInScope @AbstractName [ImportedNS] scope
  aname <- NE.toList anames
  guard $ aname.anameKind /= PatternSynName
  pure (C.QName cname, useCanonical aname.anameName)
