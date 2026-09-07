module Aegle.Index.Translate.Scope
  ( translateScope,
    collectPublicNames,
  )
where

import Aegle.Database.Backend qualified as TS
import Aegle.Index.Translate
import Aegle.Index.Translate.Definition
import Aegle.Index.Translate.Name
import Aegle.Index.Utils
import Aegle.Prelude
import Agda.Compiler.Backend
import Agda.Syntax.Concrete.Name qualified as C
import Agda.Syntax.Scope.Base
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M
import Data.Set qualified as S

--------------------------------------------------------------------------------

translateScope :: ScopeInfo -> Transl TS.LibraryFragment
translateScope scopeInfo = do
  let pubNames = collectPublicNames scopeInfo
  definitions <- forMaybe (S.toList pubNames) \aname -> do
    def <- getConstInfo aname
    translateDefinition def
  libName <- translateLibName <$> lookupModuleOrigin scopeInfo._scopeCurrent
  reexports <- for (collectReexportNames scopeInfo) \(cname, aname) -> do
    exportAs <- translateConcreteQName libName cname
    canonicalName <- translateQName aname
    pure TS.Export {..}
  let exports =
        fmap (\def -> TS.Export {canonicalName = def.name, exportAs = def.name}) definitions
          ++ reexports
  pure $! TS.LibraryFragment {..}

isNameOfTypedThing :: AbstractName -> Bool
isNameOfTypedThing aname = aname.anameKind /= PatternSynName

-- Ref: Agda.Syntax.Scope.Base.publicNames
collectPublicNames :: ScopeInfo -> S.Set QName
collectPublicNames scope =
  publicModules scope
    & M.elems
    & mergeScopes
    & namesInScope @AbstractName [PublicNS]
    & foldMap (S.fromList . NE.toList)
    & S.filter isNameOfTypedThing
    & S.mapMonotonic anameName

collectReexportNames :: ScopeInfo -> [(C.QName, QName)]
collectReexportNames scopeInfo = do
  let modul = scopeInfo._scopeCurrent
      scope = scopeInfo._scopeModules M.! scopeInfo._scopeCurrent
  (cname, anames) <- M.toList $ namesInScope @AbstractName [ImportedNS] scope
  let cname' = C.qualify (mnameToConcrete modul) cname
  aname <- NE.toList anames
  guard $ isNameOfTypedThing aname
  pure (cname', useCanonical aname.anameName)
