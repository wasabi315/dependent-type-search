{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module TypeSearch.Translate.TransparentDef
  ( translateTransparentDefBody,
  )
where

import Agda.Compiler.Backend
import Agda.Compiler.Common
import Agda.Syntax.Common
import Agda.Syntax.Internal hiding (arity)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute as Agda
import Agda.TypeChecking.Telescope
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Monad
import TypeSearch.AgdaUtils
import TypeSearch.Core.Term qualified as TS
import TypeSearch.Prelude
import TypeSearch.Translate.Common
import TypeSearch.Translate.Term

--------------------------------------------------------------------------------
-- Translate transparent definitions

hasLocalDefs :: Definition -> TransM Bool
hasLocalDefs def = do
  defs <- curDefs
  let locals =
        takeWhile (isAnonymousModuleName . qnameModule)
          $ dropWhile (<= def.defName)
          $ map fst
          $ sortDefs defs
  pure $! not (null locals)

isProjectionLike :: Definition -> TransM Bool
isProjectionLike def = do
  let Function {..} = def.theDef
  case funProjection of
    Left {} -> pure False
    Right {} -> pure True

translateTransparentDefBody :: Definition -> TransM TS.Term
translateTransparentDefBody def = do
  let Function {..} = def.theDef

  -- validation
  let bad x = translateError $ vcat [prettyTCM def.defName, x]
  whenM (hasLocalDefs def) do
    void $ bad "Not supported: transparentDef with where clause"
  whenM (isProjectionLike def) do
    void $ bad "Work-in-progress: translate projection-like definition"
  Clause {..} <- case funClauses of
    [cl] -> pure cl
    _ -> bad "Not supported: transparentDef with several clauses"

  locallyReduceTransparentDef $ translatePatternArgs def.defType namedClausePats \ty ->
    translateTerm ty (fromMaybe __IMPOSSIBLE__ clauseBody)

translatePatternArgs :: Type -> NAPs -> (Type -> TransM TS.Term) -> TransM TS.Term
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
  _ _ _ -> translateError "Not supported: transparent definition by pattern-matching"
