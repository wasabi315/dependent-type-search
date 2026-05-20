{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module TypeSearch.Translate.Term
  ( translateTerm,
    translateType,
  )
where

import Agda.Compiler.Backend hiding (Args)
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal hiding (arity, termSize)
import Agda.Syntax.Literal
import Agda.TypeChecking.Datatypes
import Agda.TypeChecking.Free
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.ProjectionLike
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute as Agda
import Agda.TypeChecking.Telescope
import Agda.Utils.Function
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Monad
import Data.Set qualified as S
import TypeSearch.AgdaUtils
import TypeSearch.Core.Term qualified as TS
import TypeSearch.Prelude
import TypeSearch.Translate.Monad
import TypeSearch.Translate.Name

--------------------------------------------------------------------------------
-- Agda Internal term/type to our Term

-- | Translate a @Type@.
translateType :: Type -> TransM TS.Term
translateType ty = translateTerm (Agda.sort $ getSort ty) ty.unEl

-- | Translate a @Term@ of a given @Type@. Reduce transparent definitions.
translateTerm :: Type -> Term -> TransM TS.Term
translateTerm ty v = do
  v <- reduceTransparentDef =<< instantiate v

  let bad s t =
        translateError
          $ vcat
            [ "cannot compile" <+> text (s ++ ":"),
              nest 2 $ prettyTCM t
            ]

  reduceProjectionLike v >>= \case
    Sort _ -> pure TS.U
    Pi a b ->
      ifM
        (isErasable a.unDom)
        do underAbstraction a b translateType
        do
          a' <- translateType a.unDom
          let name = if isBinderUsed b then realName b.absName else "_"
          addContextAndRenaming (name, a)
            $ TS.Pi (fromString name) a'
            <$> translateType (absBody b)
    Var i es -> do
      ty <- typeOfBV i
      translateSpined (translateVar i ty) (Var i) ty es
    Def f es -> maybeUnfoldCopy f es (translateTerm ty) \f es -> do
      def <- getConstInfo f
      let ty = def.defType
          f' = def.defName
      translateSpined (translateDef f' ty) (Def f') ty es
    Con ch ci es -> do
      Just ((_, _, pars), ty) <- getConType ch ty
      translateSpined (translateCon ch ci ty pars) (Con ch ci) ty es
    Lam v b -> translateLam ty v b
    Lit x -> translateLit x
    v@MetaV {} -> bad "unsolved metavariable" v
    v@DontCare {} -> bad "irrelevant term" v
    v@Dummy {} -> bad "dummy term" v
    Level {} -> __IMPOSSIBLE__

translateVar :: Int -> Type -> [Term] -> TransM TS.Term
translateVar i ty args = do
  i <- translateDBVar i
  translateApp (TS.Var i) ty args

translateDef :: QName -> Type -> [Term] -> TransM TS.Term
translateDef f ty args = case prettyShow f of
  "Agda.Builtin.Sigma.Σ" -> translateSigma ty args
  "Agda.Builtin.Sigma._,_" -> translatePair ty args
  "Agda.Builtin.Sigma.fst" -> translateFst ty args
  "Agda.Builtin.Sigma.snd" -> translateSnd ty args
  _ -> do
    let name = translateQName f
    translateApp (TS.Top name) ty args

translateSigma :: Type -> [Term] -> TransM TS.Term
translateSigma ty args =
  translateArgs ty args >>= \case
    -- fully applied
    [a, TS.Lam x b] -> do
      let x' = if 0 `S.member` TS.freeVar b then x else "_"
      pure $ TS.Sigma x' a b
    [a, b] -> pure $ TS.Sigma "x" a $ TS.weakenBy 1 b `TS.App` TS.Var 0
    -- partially applied
    [a] -> pure $ TS.Lam "B" $ TS.Sigma "x" a (TS.Var 0)
    -- unapplied
    [] -> pure $ TS.Lam "A" $ TS.Lam "B" $ TS.Sigma "x" (TS.Var 1) (TS.Var 0)
    _ -> translateError "Ill-formed sigma"

translatePair :: Type -> [Term] -> TransM TS.Term
translatePair ty args =
  translateArgs ty args >>= \case
    -- fully applied
    [a, b] -> pure $ TS.Pair a b
    -- partially applied
    [a] -> pure $ TS.Lam "x" $ TS.Pair a (TS.Var 0)
    -- unapplied
    [] -> pure $ TS.Lam "x" $ TS.Lam "y" $ TS.Pair (TS.Var 1) (TS.Var 0)
    _ -> translateError "Ill-formed pair construction"

translateFst :: Type -> [Term] -> TransM TS.Term
translateFst ty args =
  translateArgs ty args >>= \case
    -- fully applied
    p : es -> pure $! foldl' TS.App (TS.Proj1 p) es
    -- unapplied
    [] -> pure $ TS.Lam "p" $ TS.Proj1 (TS.Var 0)

translateSnd :: Type -> [Term] -> TransM TS.Term
translateSnd ty args =
  translateArgs ty args >>= \case
    -- fully applied
    p : es -> pure $! foldl' TS.App (TS.Proj2 p) es
    -- unapplied
    [] -> pure $ TS.Lam "p" $ TS.Proj2 (TS.Var 0)

translateCon :: ConHead -> ConInfo -> Type -> Args -> [Term] -> TransM TS.Term
translateCon ch i ty pars args = do
  let c = ch.conName
  conDef <- getConstInfo c
  let Constructor {..} = conDef.theDef
  if defCopy conDef
    then translateCon conSrcCon i ty pars args
    else do
      let name = translateQName conSrcCon.conName
      dataDef <- getConstInfo conData
      -- For making parameters explicit
      -- e.g) Builtin.List._∷_ x xs -> Builtin.List._∷_ A x xs
      t <- translateApp (TS.Top name) dataDef.defType $ map unArg pars
      translateApp t ty args

translateSpined ::
  ([Term] -> TransM TS.Term) ->
  (Elims -> Term) ->
  Type ->
  Elims ->
  TransM TS.Term
translateSpined c tm ty = \case
  [] -> c []
  e@(Proj o q) : es -> do
    let t = tm []
    ty' <- shouldBeProjectible t ty o q
    translateSpined (translateProj q ty t ty') (tm . (e :)) ty' es
  e@(Apply (unArg -> x)) : es -> do
    (_, b) <- mustBePi ty
    translateSpined (c . (x :)) (tm . (e :)) (absApp b x) es
  e@IApply {} : _ ->
    translateError
      $ vcat ["cannot compile interval application:", nest 2 $ prettyTCM e]

translateProj ::
  QName ->
  Type ->
  Term ->
  Type ->
  [Term] ->
  TransM TS.Term
translateProj q tty t ty args = do
  let name = translateQName q
  arg <- translateTerm tty t
  translateApp (TS.Top name `TS.App` arg) ty args

translateApp :: TS.Term -> Type -> [Term] -> TransM TS.Term
translateApp f ty args = do
  args <- translateArgs ty args
  pure $! foldl' TS.App f args

translateArgs :: Type -> [Term] -> TransM [TS.Term]
translateArgs ty args = snd <$> translateArgs' ty args

translateArgs' :: Type -> [Term] -> TransM (Type, [TS.Term])
translateArgs' ty = \case
  [] -> pure (ty, [])
  (x : xs) -> do
    (a, b) <- mustBePi ty
    let rest = translateArgs' (absApp b x) xs
    ifM
      (isErasable a.unDom)
      do rest
      do
        x <- translateTerm a.unDom x
        (ty, xs) <- rest
        pure (ty, x : xs)

translateLam :: Type -> ArgInfo -> Abs Term -> TransM TS.Term
translateLam ty _argi abs = do
  (dom, cod) <- mustBePi ty
  let name = realName abs.absName
      ctxElt = (name, dom)
  ifM
    (isErasable dom.unDom)
    do addContext ctxElt $ translateTerm (absBody cod) (absBody abs)
    do
      addContextAndRenaming ctxElt
        $ TS.Lam (fromString name)
        <$> translateTerm (absBody cod) (absBody abs)

translateLit :: Literal -> TransM TS.Term
translateLit = \case
  LitNat n -> do
    zero <- translateQName <$> getBuiltinName_ BuiltinZero
    suc <- translateQName <$> getBuiltinName_ BuiltinSuc
    pure $ iterate' n (TS.Top suc `TS.App`) (TS.Top zero)
  x -> translateError $ vcat ["cannot compile literal:", nest 2 $ prettyTCM x]
