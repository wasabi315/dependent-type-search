module TypeSearch.Database.Index.Name where

import Agda.Compiler.Backend
import Agda.Syntax.Common
import Agda.Syntax.Concrete qualified as Concrete
import Data.List.NonEmpty qualified as NonEmpty
import Data.Text qualified as T
import TypeSearch.Common qualified as TS
import TypeSearch.Database.Index.Common

--------------------------------------------------------------------------------
-- Name translation

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
