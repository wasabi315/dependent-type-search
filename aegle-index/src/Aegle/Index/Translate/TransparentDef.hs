{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Aegle.Index.Translate.TransparentDef
  ( translateTransparentDefBody,
  )
where

import Aegle.Core.Term qualified as TS
import Aegle.Index.Translate
import Aegle.Index.Translate.Term
import Aegle.Index.Utils
import Aegle.Prelude
import Agda.Compiler.Backend
import Agda.Syntax.Common
import Agda.Syntax.Internal hiding (arity)
import Agda.TypeChecking.Substitute as Agda
import Agda.TypeChecking.Telescope
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Monad

--------------------------------------------------------------------------------
-- Translate transparent definitions

-- | Expects non-pattern-matching definitions.
translateTransparentDefBody :: Definition -> Transl TS.Term
translateTransparentDefBody def = do
  let Function {..} = def.theDef

  -- validation
  Clause {..} <- case funClauses of
    [cl] -> pure cl
    _ -> __IMPOSSIBLE__

  translatePatternArgs def.defType namedClausePats \ty ->
    translateTerm ty (fromMaybe __IMPOSSIBLE__ clauseBody)

translatePatternArgs :: Type -> NAPs -> (Type -> Transl TS.Term) -> Transl TS.Term
translatePatternArgs = \cases
  ty [] k -> k ty
  ty ((namedArg -> (VarP _ x)) : ps) k -> do
    (dom, cod) <- mustBePi ty
    let varName = realName x.dbPatVarName
        ctxElt = (KeepNames varName, dom)
    ifM
      (isErasable dom.unDom)
      do addContext ctxElt $ translatePatternArgs (absBody cod) ps k
      do
        addContextAndRenaming ctxElt
          $ TS.Lam (fromString varName)
          <$> translatePatternArgs (absBody cod) ps k
  _ _ _ -> __IMPOSSIBLE__
