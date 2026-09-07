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
import Data.Text qualified as T
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

--------------------------------------------------------------------------------

-- | Note that these identifiers are not filtered against the query parser's
-- reserved tokens, since that is a parser concern and this library sits below
-- it. A test that round-trips through the parser should wrap the generator
-- itself, e.g. @Gen.filterT (not . keyword . coerce) genName@.
genIdent :: Gen T.Text
genIdent = Gen.text (Range.constant 1 4) Gen.alpha

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
