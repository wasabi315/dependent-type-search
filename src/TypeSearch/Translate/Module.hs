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
import TypeSearch.Core.Module qualified as TS
import TypeSearch.Prelude
import TypeSearch.Translate.Definition
import TypeSearch.Translate.Monad
import TypeSearch.Translate.Name

--------------------------------------------------------------------------------

translateScope :: ScopeInfo -> Transl TS.Module
translateScope scopeInfo = do
  definitions <- forMaybe (collectPublicNames scopeInfo) \(cname, aname) ->
    getConstInfo' aname >>= \case
      Left _ -> pure Nothing
      Right def -> do
        let name =
              translateConcreteQName
                (translateModuleName scopeInfo._scopeCurrent)
                cname
        translateDefinition name def
  pure $! TS.Module {..}

collectPublicNames :: ScopeInfo -> [(C.QName, QName)]
collectPublicNames scopeInfo = DL.toList $ go id $ getScope scopeInfo._scopeCurrent
  where
    getScope m = scopeInfo._scopeModules M.! m

    go _ scope
      | Just IsDataModule <- scope.scopeDatatypeModule = mempty
    go qual scope = names <> namesInChildren
      where
        names = do
          (cname, anames) <-
            DL.fromList $
              M.toList $
                namesInScope @AbstractName [PublicNS] scope
          aname <- DL.fromList $ NE.toList anames
          pure (qual (C.QName cname), aname.anameName)

        namesInChildren = do
          (cmodName, amods) <-
            DL.fromList $
              M.toList $
                namesInScope @AbstractModule [PublicNS] scope
          amod <- DL.fromList $ NE.toList amods
          go (qual . C.Qual cmodName) (getScope amod.amodName)
