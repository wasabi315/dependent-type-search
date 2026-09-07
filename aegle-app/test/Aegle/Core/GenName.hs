module Aegle.Core.GenName
  ( genName,
    genModuleName,
    genLibName,
    genQName,
    genPQName,
  )
where

import Aegle.Core.Name
import Aegle.Prelude
import Aegle.Search.Parser (keyword)
import Data.Text qualified as T
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

--------------------------------------------------------------------------------

genIdent :: Gen T.Text
genIdent = Gen.filterT (not . keyword) do
  Gen.text (Range.constant 1 4) Gen.alpha

genName :: Gen Name
genName = Name <$> genIdent

genModuleName :: Gen ModuleName
genModuleName = ModuleName <$> genIdent

genLibName :: Gen LibName
genLibName = LibName <$> genIdent

genQName :: Gen QName
genQName = QName <$> genLibName <*> genModuleName <*> genName

genPQName :: Gen PQName
genPQName =
  Gen.choice
    [ Unqual <$> genName,
      Qual <$> genModuleName <*> genName
    ]
