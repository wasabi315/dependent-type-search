module TypeSearch.Database.Index.Name
  ( translateModuleName,
    translateTopLevelModuleName,
    translateQName,
    translateConcreteQName,
    translateName,
  )
where

import Agda.Compiler.Backend
import Agda.Syntax.Common
import Agda.Syntax.Concrete qualified as C
import Data.List.NonEmpty qualified as NE
import Data.Text qualified as T
import TypeSearch.Core.Name qualified as TS
import TypeSearch.Prelude

--------------------------------------------------------------------------------
-- Name translation

translateModuleName :: ModuleName -> TS.ModuleName
translateModuleName m =
  TS.ModuleName
    $ T.intercalate "."
    $ map (T.pack . C.nameToRawName . nameConcrete)
    $ filter (not . isNoName)
    $ mnameToList m

translateTopLevelModuleName :: TopLevelModuleName -> TS.ModuleName
translateTopLevelModuleName =
  TS.ModuleName
    . T.intercalate "."
    . NE.toList
    . moduleNameParts

translateQName :: QName -> TS.QName
translateQName f = do
  let x = translateName $ nameConcrete $ qnameName f
      m = translateModuleName $ qnameModule f
  TS.QName m x

translateConcreteQName :: TS.ModuleName -> C.QName -> TS.QName
translateConcreteQName ini = go (coerce ini)
  where
    go acc = \case
      C.QName x -> TS.QName (TS.ModuleName acc) (translateName x)
      C.Qual m x -> go (acc <> "." <> coerce (translateName m)) x

translateName :: C.Name -> TS.Name
translateName = TS.Name . T.pack . C.nameToRawName
