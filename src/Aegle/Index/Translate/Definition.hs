module Aegle.Index.Translate.Definition
  ( translateDefinition,
  )
where

import Aegle.Core.Evaluation qualified as TS
import Aegle.Core.Isomorphism qualified as TS
import Aegle.Core.Name qualified as TS
import Aegle.Core.Term qualified as TS
import Aegle.Database.Backend qualified as TS
import Aegle.Index.Translate
import Aegle.Index.Translate.Name
import Aegle.Index.Translate.Term
import Aegle.Index.Translate.TransparentDef
import Aegle.Index.Utils
import Aegle.Prelude
import Aegle.Search.Feature qualified as TS
import Agda.Compiler.Backend
import Agda.Syntax.Position
import Agda.Utils.Monad hiding (guard, unless)

--------------------------------------------------------------------------------

translateDefinition :: Definition -> Transl (Maybe TS.Definition)
translateDefinition def = setCurrentRangeQ def.defName do
  ifM (isErasable def.defType) (pure Nothing) case def.theDef of
    AxiomDefn {} -> Just <$> translateToAxiom def
    AbstractDefn {} -> Just <$> translateToAxiom def
    FunctionDefn {} -> Just <$> translateFunDef def
    DatatypeDefn {} -> Just <$> translateToAxiom def
    RecordDefn {} -> Just <$> translateToAxiom def
    ConstructorDefn {} -> Just <$> translateToAxiom def
    PrimitiveDefn {} -> Just <$> translateToAxiom def
    DataOrRecSigDefn {} -> pure Nothing
    GeneralizableVar {} -> pure Nothing
    PrimitiveSortDefn {} -> pure Nothing

getKind :: Defn -> TS.DefKind
getKind = \case
  AbstractDefn defn -> getKind defn
  AxiomDefn {} -> TS.DKPostulate
  FunctionDefn {} -> TS.DKFunction
  DatatypeDefn {} -> TS.DKDatatype
  RecordDefn {} -> TS.DKRecord
  ConstructorDefn {} -> TS.DKConstructor
  PrimitiveDefn {} -> TS.DKPrimitive
  (DataOrRecSigDefn {}; GeneralizableVar {}; PrimitiveSortDefn {}) ->
    error "getKind: unsupported definition kind"

translateToAxiom :: Definition -> Transl TS.Definition
translateToAxiom def = do
  name <- translateQName def.defName
  let kind = getKind def.theDef
      (moduleName, position) = bindingSite def.defName
  signature <- translateType def.defType
  originalSignature <- withAllDefsOpaque $ translateType def.defType
  pure $! constructDefinition Definition' {body = Nothing, ..}

translateFunDef :: Definition -> Transl TS.Definition
translateFunDef def = do
  name <- translateQName def.defName
  let (moduleName, position) = bindingSite def.defName
  signature <- translateType def.defType
  originalSignature <- withAllDefsOpaque $ translateType def.defType
  body <- ifM
    (isTransparentDef def.defName)
    do Just <$> translateTransparentDefBody def
    do pure Nothing
  pure $! constructDefinition Definition' {kind = TS.DKFunction, ..}

bindingSite :: QName -> (TS.ModuleName, Int)
bindingSite qname = (moduleName, position)
  where
    range = qname.qnameName.nameBindingSite
    moduleName = translateTopLevelModuleName $ fromJust $ rangeModule range
    -- Ref: Agda.Interaction.Highlighting.HTML.Base.annotate
    position = fromIntegral $ posPos $ fromJust $ rStart range

data Definition' = Definition'
  { name :: TS.QName,
    kind :: TS.DefKind,
    signature :: TS.Type,
    originalSignature :: TS.Type,
    body :: Maybe TS.Term,
    moduleName :: TS.ModuleName,
    position :: Int
  }

constructDefinition ::
  Definition' ->
  TS.Definition
constructDefinition Definition' {..} = TS.Definition {..}
  where
    (signature', _) = TS.normalise0 (TS.emptyMetaCtx mempty) signature
    feature = TS.allFeature signature'
