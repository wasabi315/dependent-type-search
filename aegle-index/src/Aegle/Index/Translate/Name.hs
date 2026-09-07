module Aegle.Index.Translate.Name
  ( translateModuleName,
    translateTopLevelModuleName,
    translateQName,
    translateConcreteQName,
    translateName,
    translateLibName,
  )
where

import Aegle.Core.Name qualified as TS
import Aegle.Index.Translate
import Aegle.Prelude
import Agda.Compiler.Backend
import Agda.Interaction.Library.Base
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty
import Agda.Syntax.Concrete qualified as C
import Data.List.NonEmpty qualified as NE
import Data.Text qualified as T

--------------------------------------------------------------------------------
-- Name translation

translateLibName :: LibName -> TS.LibName
translateLibName = coerce . T.show . pretty

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

translateQName :: QName -> Transl TS.QName
translateQName f = do
  lib <- lookupModuleOrigin f.qnameModule
  let l = translateLibName lib
      x = translateName $ nameConcrete $ qnameName f
      m = translateModuleName $ qnameModule f
  pure $ TS.QName l m x

translateConcreteQName :: TS.LibName -> C.QName -> Transl TS.QName
translateConcreteQName lib = go ""
  where
    go acc = \case
      C.QName x -> do
        let m = TS.ModuleName $ T.tail acc -- to remove initial dot
            x' = translateName x
        pure $ TS.QName lib m x'
      C.Qual m x -> go (acc <> "." <> coerce (translateName m)) x

translateName :: C.Name -> TS.Name
translateName = TS.Name . T.pack . C.nameToRawName
