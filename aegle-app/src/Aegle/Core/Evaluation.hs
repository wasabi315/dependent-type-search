module Aegle.Core.Evaluation
  ( module Aegle.Core.Evaluation,
  )
where

import Aegle.Core.Name
import Aegle.Core.Term
import Aegle.Prelude
import Data.IntMap.Strict qualified as IM
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Prettyprinter

--------------------------------------------------------------------------------
-- Values

-- | Values
data Value
  = VRigid Level Spine
  | VFlex MetaVar Spine
  | VOpaque {-# UNPACK #-} QName Spine
  | VAmb PQName Spine
  | VU
  | VPi Name VType (Value -> VType)
  | VLam Name (Value -> Value)
  | VSigma Name VType (Value -> VType)
  | VPair Value Value
  | VBrave Value Spine

type VType = Value

data Spine
  = SNil
  | SApp Spine Value
  | SProj1 Spine
  | SProj2 Spine

pattern VVar :: Level -> Value
pattern VVar x = VRigid x SNil

pattern VMeta :: MetaVar -> Value
pattern VMeta m = VFlex m SNil

data Quant = Quant Name Value (Value -> Value)

type Env = [Value]

data TopEnvEntry = TopEnvEntry
  { opaques :: S.Set QName,
    transps :: [Value]
  }

-- | Meta-context
data MetaCtx = MetaCtx
  { nextMeta :: MetaVar,
    metaCtx :: IM.IntMap MetaEntry,
    resol :: Resol
  }
  deriving stock (Generic)

data MetaEntry
  = Unsolved ~VType
  | Solved Value ~VType

type Resol = M.Map PQName ResolEntry

data ResolEntry
  = Unresolved (S.Set QName) [Value]
  | ResolvedOpaque QName
  | ResolvedTransp Value

--------------------------------------------------------------------------------
-- Meta-context operation

emptyMetaCtx :: Resol -> MetaCtx
emptyMetaCtx = MetaCtx 0 mempty

newMeta :: MetaCtx -> VType -> (MetaVar, MetaCtx)
newMeta mctx ~mty = do
  let m' = mctx.nextMeta
      mctx' =
        mctx
          { nextMeta = mctx.nextMeta + 1,
            metaCtx = IM.insert (coerce m') (Unsolved mty) mctx.metaCtx
          }
  (m', mctx')

allMetaSolved :: MetaCtx -> Bool
allMetaSolved mctx = flip all mctx.metaCtx \case
  Unsolved {} -> False
  Solved {} -> True

lookupUnsolved :: MetaCtx -> MetaVar -> Value
lookupUnsolved mctx m = case mctx.metaCtx IM.! coerce m of
  Unsolved a -> a
  Solved {} -> error "lookupUnsolved"

writeMeta :: MetaCtx -> MetaVar -> Value -> VType -> MetaCtx
writeMeta mctx m t ~a =
  mctx
    { metaCtx = IM.insert (coerce m) (Solved t a) mctx.metaCtx
    }

resolveOpaque :: MetaCtx -> PQName -> QName -> MetaCtx
resolveOpaque mctx x y =
  mctx
    { resol = M.insert x (ResolvedOpaque y) mctx.resol
    }

resolveTransp :: MetaCtx -> PQName -> Value -> MetaCtx
resolveTransp mctx x t =
  mctx
    { resol = M.insert x (ResolvedTransp t) mctx.resol
    }

opaqueOnly :: MetaCtx -> PQName -> S.Set QName -> MetaCtx
opaqueOnly mctx x xs =
  mctx
    { resol = M.insert x (Unresolved xs []) mctx.resol
    }

lookupResol :: MetaCtx -> PQName -> ResolEntry
lookupResol mctx x = mctx.resol M.! x
{-# INLINE lookupResol #-}

--------------------------------------------------------------------------------
-- Evaluation

idEnv :: Level -> Env
idEnv l = VVar <$> (l - 1) `down` 0

eval :: MetaCtx -> Env -> Term -> Value
eval mctx env = \case
  Var (Index x) -> env !! x
  Meta m -> vMeta mctx m
  Opaque x -> VOpaque x SNil
  Amb x -> vAmb mctx x
  U -> VU
  Pi x a b -> VPi x (eval mctx env a) (evalBind mctx env b)
  Lam x t -> VLam x (evalBind' mctx env t)
  App t u -> eval mctx env t $$ eval mctx env u
  Sigma x a b -> VSigma x (eval mctx env a) (evalBind mctx env b)
  Pair t u -> VPair (eval mctx env t) (eval mctx env u)
  Proj1 t -> vProj1 (eval mctx env t)
  Proj2 t -> vProj2 (eval mctx env t)
  AppPruning t pr -> vAppPruning env (eval mctx env t) pr

evalBind :: MetaCtx -> Env -> Term -> (Value -> Value)
evalBind mctx env t ~u = eval mctx (u : env) t

evalBind' :: MetaCtx -> Env -> Term -> (Value -> Value)
evalBind' mctx env t u = eval mctx (u : env) t

vMeta :: MetaCtx -> MetaVar -> Value
vMeta mctx m = case mctx.metaCtx IM.! coerce m of
  Unsolved {} -> VMeta m
  Solved v _ -> v

vAmb :: MetaCtx -> PQName -> Value
vAmb mctx x = case mctx.resol M.! x of
  Unresolved {} -> VAmb x SNil
  ResolvedOpaque x -> VOpaque x SNil
  ResolvedTransp t -> t

vAppPruning :: Env -> Value -> Pruning -> Value
vAppPruning env ~v pr = case (env, pr) of
  ([], []) -> v
  (t : env, True : pr) -> vAppPruning env v pr $$ t
  (_ : env, False : pr) -> vAppPruning env v pr
  _ -> impossible "vAppPruning"

($$) :: Value -> Value -> Value
t $$ u = case t of
  VLam _ t -> t u
  VRigid x sp -> VRigid x (SApp sp u)
  VFlex m sp -> VFlex m (SApp sp u)
  VOpaque x sp -> VOpaque x (SApp sp u)
  VAmb x sp -> VAmb x (SApp sp u)
  VBrave b sp -> VBrave b (SApp sp u)
  t -> VBrave t (SApp SNil u)

vProj1 :: Value -> Value
vProj1 = \case
  VPair t _ -> t
  VRigid x sp -> VRigid x (SProj1 sp)
  VFlex m sp -> VFlex m (SProj1 sp)
  VOpaque x sp -> VOpaque x (SProj1 sp)
  VAmb x sp -> VAmb x (SProj1 sp)
  VBrave b sp -> VBrave b (SProj1 sp)
  t -> VBrave t (SProj1 SNil)

vProj2 :: Value -> Value
vProj2 = \case
  VPair _ t -> t
  VRigid x sp -> VRigid x (SProj2 sp)
  VFlex m sp -> VFlex m (SProj2 sp)
  VOpaque x sp -> VOpaque x (SProj2 sp)
  VAmb x sp -> VAmb x (SProj2 sp)
  VBrave b sp -> VBrave b (SProj2 sp)
  t -> VBrave t (SProj2 SNil)

vAppSpine :: Value -> Spine -> Value
vAppSpine t = \case
  SNil -> t
  SApp sp u -> vAppSpine t sp $$ u
  SProj1 sp -> vProj1 $ vAppSpine t sp
  SProj2 sp -> vProj2 $ vAppSpine t sp

force :: MetaCtx -> Value -> Value
force mctx = \case
  VFlex m sp
    | Solved t _ <- mctx.metaCtx IM.! coerce m ->
        force mctx (vAppSpine t sp)
  t@(VAmb x sp) -> case mctx.resol M.! x of
    ResolvedOpaque x -> VOpaque x sp
    ResolvedTransp t -> force mctx (vAppSpine t sp)
    Unresolved {} -> t
  t -> t

-- | Choose resolution for an unresolved ambiguous name
chooseAmb :: MetaCtx -> PQName -> Spine -> S.Set QName -> [Value] -> [(Value, MetaCtx)]
chooseAmb mctx x sp xs ts =
  concat
    [ do
        guard $ not (S.null xs) && not (null ts)
        let mctx' = opaqueOnly mctx x xs
        pure (VAmb x sp, mctx'),
      do
        t <- ts
        let mctx' = resolveTransp mctx x t
        pure (vAppSpine t sp, mctx')
    ]
{-# INLINE chooseAmb #-}

forceNondet :: MetaCtx -> Value -> [(Value, MetaCtx)]
forceNondet mctx = \case
  VFlex m sp
    | Solved t _ <- mctx.metaCtx IM.! coerce m ->
        forceNondet mctx (vAppSpine t sp)
  t@(VAmb x sp) -> case lookupResol mctx x of
    ResolvedOpaque y -> pure (VOpaque y sp, mctx)
    ResolvedTransp u -> forceNondet mctx (vAppSpine u sp)
    -- already opaque
    Unresolved _ [] -> pure (t, mctx)
    Unresolved xs ts@(_ : _) ->
      concat
        [ do
            guard $ not $ S.null xs
            let mctx' = opaqueOnly mctx x xs
            pure (t, mctx'),
          do
            u <- ts
            let mctx' = resolveTransp mctx x u
            forceNondet mctx' (vAppSpine u sp)
        ]
  t -> pure (t, mctx)

--------------------------------------------------------------------------------
-- Quotation

levelToIndex :: Level -> Level -> Index
levelToIndex (Level l) (Level x) = Index (l - x - 1)

quote :: MetaCtx -> Level -> Value -> Term
quote mctx l t = case force mctx t of
  VRigid x sp -> quoteSpine mctx l (Var (levelToIndex l x)) sp
  VFlex m sp -> quoteSpine mctx l (Meta m) sp
  VOpaque x sp -> quoteSpine mctx l (Opaque x) sp
  VAmb x sp -> quoteSpine mctx l (Amb x) sp
  VU -> U
  VPi x a b -> Pi x (quote mctx l a) (quoteBind mctx l b)
  VLam x t -> Lam x (quoteBind mctx l t)
  VSigma x a b -> Sigma x (quote mctx l a) (quoteBind mctx l b)
  VPair t u -> Pair (quote mctx l t) (quote mctx l u)
  VBrave t sp -> quoteSpine mctx l (quote mctx l t) sp

quoteBind :: MetaCtx -> Level -> (Value -> Value) -> Term
quoteBind mctx l b = quote mctx (l + 1) (b $ VVar l)

quoteSpine :: MetaCtx -> Level -> Term -> Spine -> Term
quoteSpine mctx l h = \case
  SNil -> h
  SApp sp u -> quoteSpine mctx l h sp `App` quote mctx l u
  SProj1 sp -> Proj1 $ quoteSpine mctx l h sp
  SProj2 sp -> Proj2 $ quoteSpine mctx l h sp

quoteNondet :: MetaCtx -> Level -> Value -> [(Term, MetaCtx)]
quoteNondet mctx l t = do
  (t, mctx) <- forceNondet mctx t
  case t of
    VRigid x sp -> quoteSpineNondet mctx l (Var (levelToIndex l x)) sp
    VFlex m sp -> quoteSpineNondet mctx l (Meta m) sp
    VOpaque x sp -> quoteSpineNondet mctx l (Opaque x) sp
    VAmb x sp -> quoteSpineNondet mctx l (Amb x) sp
    VU -> pure (U, mctx)
    VPi x a b -> do
      (a, mctx) <- quoteNondet mctx l a
      (b, mctx) <- quoteBindNondet mctx l b
      pure (Pi x a b, mctx)
    VLam x t -> do
      (t, mctx) <- quoteBindNondet mctx l t
      pure (Lam x t, mctx)
    VSigma x a b -> do
      (a, mctx) <- quoteNondet mctx l a
      (b, mctx) <- quoteBindNondet mctx l b
      pure (Sigma x a b, mctx)
    VPair t u -> do
      (t, mctx) <- quoteNondet mctx l t
      (u, mctx) <- quoteNondet mctx l u
      pure (Pair t u, mctx)
    VBrave {} -> []

quoteBindNondet :: MetaCtx -> Level -> (Value -> Value) -> [(Term, MetaCtx)]
quoteBindNondet mctx l b = quoteNondet mctx (l + 1) (b $ VVar l)

quoteSpineNondet :: MetaCtx -> Level -> Term -> Spine -> [(Term, MetaCtx)]
quoteSpineNondet mctx l h = \case
  SNil -> pure (h, mctx)
  SApp sp u -> do
    (t, mctx) <- quoteSpineNondet mctx l h sp
    (u, mctx) <- quoteNondet mctx l u
    pure (App t u, mctx)
  SProj1 sp -> do
    (t, mctx) <- quoteSpineNondet mctx l h sp
    pure (Proj1 t, mctx)
  SProj2 sp -> do
    (t, mctx) <- quoteSpineNondet mctx l h sp
    pure (Proj2 t, mctx)

--------------------------------------------------------------------------------
-- Prettyprinting

instance Pretty TopEnvEntry where
  pretty TopEnvEntry {..} =
    group
      $ encloseSep (flatAlt "{ " "{") (flatAlt " }" "}") ", "
      $ [ pretty x
        | x <- S.toList opaques
        ]
      ++ [ pretty ((emptyMetaCtx mempty, Level 0) :⊢ t)
         | t <- transps
         ]

instance Pretty MetaCtx where
  pretty mctx =
    group
      $ encloseSep (flatAlt "{ " "{") (flatAlt " }" "}") ", "
      $ [ pretty (MetaVar m)
            <+> "="
            <+> maybe "?" (pretty . ((mctx, Level 0) :⊢)) sol
        | (m, entry) <- IM.toList mctx.metaCtx,
          let sol = case entry of
                Solved t _ -> Just t
                Unsolved _ -> Nothing
        ]
      ++ [ pretty x <+> case entry of
             Unresolved xs ts ->
               "∈"
                 <+> pretty (S.size xs)
                 <+> "opaque(s),"
                 <+> pretty (length ts)
                 <+> "transparent"
             ResolvedOpaque y -> "=" <+> pretty y
             ResolvedTransp t -> "=" <+> pretty ((mctx, Level 0) :⊢ t)
         | (x, entry) <- M.toList mctx.resol
         ]

instance Pretty ((MetaCtx, Level) ⊢ Value) where
  pretty ((mctx, lvl) :⊢ v) = pretty $ quote mctx lvl v

instance Pretty ((MetaCtx, [Name]) ⊢ Value) where
  pretty ((mctx, ns) :⊢ v) = pretty (ns :⊢ quote mctx (coerce $ length ns) v)
