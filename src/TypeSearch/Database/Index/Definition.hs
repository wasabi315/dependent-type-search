module TypeSearch.Database.Index.Definition
  ( translateDefinition,
  )
where

import Agda.Compiler.Backend
import Agda.Syntax.Internal hiding (arity)
import Agda.Utils.Monad hiding (unless)
import TypeSearch.Core.Name qualified as TS
import TypeSearch.Core.Term qualified as TS
import TypeSearch.Database.Index.Common
import TypeSearch.Database.Index.Term
import TypeSearch.Database.Index.TransparentDef
import TypeSearch.Prelude

--------------------------------------------------------------------------------

translateDefinition :: TS.QName -> Definition -> M (Maybe TS.Definition)
translateDefinition qname def = setCurrentRangeQ def.defName do
  ifM
    (orM [isErasable def.defType, isDeprecated def.defName])
    do pure Nothing
    case def.theDef of
      AxiomDefn {} -> Just <$> translateToAxiom qname def.defType
      AbstractDefn {} -> Just <$> translateToAxiom qname def.defType
      FunctionDefn {} -> Just <$> translateFunDef qname def
      DatatypeDefn {} -> Just <$> translateToAxiom qname def.defType
      RecordDefn {} -> Just <$> translateToAxiom qname def.defType
      ConstructorDefn {} -> Just <$> translateToAxiom qname def.defType
      PrimitiveDefn {} -> Just <$> translateToAxiom qname def.defType
      DataOrRecSigDefn {} -> pure Nothing
      GeneralizableVar {} -> pure Nothing
      PrimitiveSortDefn {} -> pure Nothing

translateToAxiom :: TS.QName -> Type -> M TS.Definition
translateToAxiom name sig = do
  sig <- locallyReduceTransparentDef $ translateType sig
  pure $ TS.Definition {body = Nothing, ..}

translateFunDef :: TS.QName -> Definition -> M TS.Definition
translateFunDef name def = do
  sig <- locallyReduceTransparentDef $ translateType def.defType
  body <- ifM
    (isTransparentDef def.defName)
    do Just <$> translateTransparentDefBody def
    do pure Nothing
  pure $ TS.Definition {..}
