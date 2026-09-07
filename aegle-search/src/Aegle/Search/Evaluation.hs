module Aegle.Search.Evaluation
  ( Value (..),
    VType,
    Head (..),
    Spine (..),
    pattern VVar,
    VQuant (..),
    Env,
    MetaCtx (..),
    MetaEntry (..),
    ResolEntry (..),
    ($$),
    vProj1,
    vProj2,
    pattern (:*),
    evalQuery,
    evalCore,
    eval,
    idEnv,
    emptyMetaCtx,
    newMeta,
    allMetaSolved,
    lookupUnsolved,
    lookupResol,
    writeMeta,
    resolveOpaque,
    resolveTransp,
    opaqueOnly,
    force,
    chooseAmb,
    forceNondet,
    quote,
    quoteNondet,
  )
where

import Aegle.Core.Evaluation (pattern (:>))
import Aegle.Core.Name
import Aegle.Core.Term (Unqualified (..))
import Aegle.Core.Term qualified as C
import Aegle.Prelude
import Aegle.Search.Query qualified as Q
import Aegle.Search.Term
import Data.IntMap.Strict qualified as IM
import Data.Map.Strict qualified as M
import Data.Set qualified as S
import Prettyprinter

infixr 4 :*

--------------------------------------------------------------------------------

-- | Values
data Value
  = VNe Head Spine
  | VU
  | VPi Name VType (Value -> VType)
  | VLam Name (Value -> Value)
  | VSigma Name VType (Value -> VType)
  | VPair Value Value
  | VBrave Value Spine

type VType = Value

data Head
  = HRigid Level
  | HOpaque QName
  | HAmb PQName
  | HFlex MetaVar
  deriving stock (Eq, Show)

data Spine
  = SNil
  | SApp Spine Value
  | SProj1 Spine
  | SProj2 Spine

pattern VVar :: Level -> Value
pattern VVar x = VNe (HRigid x) SNil

data VQuant = VQuant Name VType (Value -> VType)

type Env = [Value]

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

($$) :: Value -> Value -> Value
t $$ u = case t of
  VLam _ t -> t u
  VNe h sp -> VNe h (SApp sp u)
  VBrave t sp -> VBrave t (SApp sp u)
  t -> VBrave t (SApp SNil u)

vProj1 :: Value -> Value
vProj1 = \case
  VPair t _ -> t
  VNe h sp -> VNe h (SProj1 sp)
  VBrave t sp -> VBrave t (SProj1 sp)
  t -> VBrave t (SProj1 SNil)

vProj2 :: Value -> Value
vProj2 = \case
  VPair _ t -> t
  VNe h sp -> VNe h (SProj2 sp)
  VBrave t sp -> VBrave t (SProj2 sp)
  t -> VBrave t (SProj2 SNil)

vMeta :: MetaCtx -> MetaVar -> Value
vMeta mctx m = case mctx.metaCtx IM.! coerce m of
  Unsolved {} -> VNe (HFlex m) SNil
  Solved v _ -> v

vAmb :: MetaCtx -> PQName -> Value
vAmb mctx x = case mctx.resol M.! x of
  Unresolved {} -> VNe (HAmb x) SNil
  ResolvedOpaque x -> VNe (HOpaque x) SNil
  ResolvedTransp t -> t

vAppSpine :: Value -> Spine -> Value
vAppSpine t = \case
  SNil -> t
  SApp sp u -> vAppSpine t sp $$ u
  SProj1 sp -> vProj1 $ vAppSpine t sp
  SProj2 sp -> vProj2 $ vAppSpine t sp

vAppPruning :: Env -> Value -> Pruning -> Value
vAppPruning env ~v pr = case (env, pr) of
  ([], []) -> v
  (t : env, True : pr) -> vAppPruning env v pr $$ t
  (_ : env, False : pr) -> vAppPruning env v pr
  _ -> impossible "vAppPruning"

-- sugars

instance HasField "p1" Value Value where
  getField = vProj1
  {-# INLINE getField #-}

instance HasField "p2" Value Value where
  getField = vProj2
  {-# INLINE getField #-}

vUnpair :: Value -> (Value, Value)
vUnpair = \case
  VPair t u -> (t, u)
  VNe h sp -> (VNe h (SProj1 sp), VNe h (SProj2 sp))
  VBrave t sp -> (VBrave t (SProj1 sp), VBrave t (SProj2 sp))
  t -> (VBrave t (SProj1 SNil), VBrave t (SProj2 SNil))

pattern (:*) :: Value -> Value -> Value
pattern t :* u <- (vUnpair -> (t, u))
  where
    t :* u = VPair t u

{-# COMPLETE (:*) #-}

{-# INLINE (:*) #-}

--------------------------------------------------------------------------------
-- Metacontext operations

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
-- NbE

idEnv :: Level -> Env
idEnv l = VVar <$> (l - 1) `down` 0

evalCore :: [Value] -> C.Term -> Value
evalCore env = \case
  C.Var (Index x) -> env !! x
  C.Opaque x -> VNe (HOpaque x) SNil
  C.U -> VU
  C.Pi x a b -> VPi x (evalCore env a) \ ~t -> evalCore (env :> t) b
  C.Lam x t -> VLam x \u -> evalCore (env :> u) t
  C.App t u -> evalCore env t $$ evalCore env u
  C.Sigma x a b -> VSigma x (evalCore env a) \ ~t -> evalCore (env :> t) b
  C.Pair t u -> VPair (evalCore env t) (evalCore env u)
  C.Proj1 t -> vProj1 (evalCore env t)
  C.Proj2 t -> vProj2 (evalCore env t)

evalQuery :: [(Name, Value)] -> Q.Term -> Value
evalQuery env = \case
  Q.Var (Unqual x)
    | Just t <- lookup x env -> t
  Q.Var x -> VNe (HAmb x) SNil
  Q.U -> VU
  Q.Pi x a b -> do
    let x' = if Unqual x `S.member` Q.freeVars b then x else "_"
    VPi x' (evalQuery env a) \ ~v -> evalQuery (env :> (x', v)) b
  Q.Lam x t -> VLam x \v -> evalQuery (env :> (x, v)) t
  Q.App t u -> evalQuery env t $$ evalQuery env u
  Q.Sigma x a b -> do
    let x' = if Unqual x `S.member` Q.freeVars b then x else "_"
    VSigma x' (evalQuery env a) \ ~v -> evalQuery (env :> (x', v)) b
  Q.Pair t u -> evalQuery env t `VPair` evalQuery env u
  Q.Proj1 t -> vProj1 (evalQuery env t)
  Q.Proj2 t -> vProj2 (evalQuery env t)

eval :: MetaCtx -> Env -> Term -> Value
eval mctx env = \case
  Var (Index x) -> env !! x
  Meta m -> vMeta mctx m
  Opaque x -> VNe (HOpaque x) SNil
  Amb x -> vAmb mctx x
  U -> VU
  Pi x a b -> VPi x (eval mctx env a) \ ~t -> eval mctx (env :> t) b
  Lam x t -> VLam x \u -> eval mctx (env :> u) t
  App t u -> eval mctx env t $$ eval mctx env u
  Sigma x a b -> VSigma x (eval mctx env a) \ ~t -> eval mctx (env :> t) b
  Pair t u -> VPair (eval mctx env t) (eval mctx env u)
  Proj1 t -> vProj1 (eval mctx env t)
  Proj2 t -> vProj2 (eval mctx env t)
  AppPruning t pr -> vAppPruning env (eval mctx env t) pr

force :: MetaCtx -> Value -> Value
force mctx = \case
  VNe (HFlex m) sp
    | Solved t _ <- mctx.metaCtx IM.! coerce m ->
        force mctx (vAppSpine t sp)
  t@(VNe (HAmb x) sp) -> case mctx.resol M.! x of
    ResolvedOpaque x -> VNe (HOpaque x) sp
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
        pure (VNe (HAmb x) sp, mctx'),
      do
        t <- ts
        let mctx' = resolveTransp mctx x t
        pure (vAppSpine t sp, mctx')
    ]
{-# INLINE chooseAmb #-}

forceNondet :: MetaCtx -> Value -> [(Value, MetaCtx)]
forceNondet mctx = \case
  VNe (HFlex m) sp
    | Solved t _ <- mctx.metaCtx IM.! coerce m ->
        forceNondet mctx (vAppSpine t sp)
  t@(VNe (HAmb x) sp) -> case lookupResol mctx x of
    ResolvedOpaque y -> pure (VNe (HOpaque y) sp, mctx)
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

quote :: MetaCtx -> Level -> Value -> Term
quote mctx l t = case force mctx t of
  VNe h sp -> quoteSpine mctx l (quoteHead l h) sp
  VU -> U
  VPi x a b -> Pi x (quote mctx l a) (quote mctx (l + 1) (b $ VVar l))
  VLam x t -> Lam x (quote mctx (l + 1) (t $ VVar l))
  VSigma x a b -> Sigma x (quote mctx l a) (quote mctx (l + 1) (b $ VVar l))
  VPair t u -> Pair (quote mctx l t) (quote mctx l u)
  VBrave t sp -> quoteSpine mctx l (quote mctx l t) sp

quoteHead :: Level -> Head -> Term
quoteHead l = \case
  HRigid x -> Var (levelToIndex l x)
  HFlex m -> Meta m
  HOpaque x -> Opaque x
  HAmb x -> Amb x

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
    VNe h sp -> quoteSpineNondet mctx l (quoteHead l h) sp
    VU -> pure (U, mctx)
    VPi x a b -> do
      (a, mctx) <- quoteNondet mctx l a
      (b, mctx) <- quoteNondet mctx (l + 1) (b $ VVar l)
      pure (Pi x a b, mctx)
    VLam x t -> do
      (t, mctx) <- quoteNondet mctx (l + 1) (t $ VVar l)
      pure (Lam x t, mctx)
    VSigma x a b -> do
      (a, mctx) <- quoteNondet mctx l a
      (b, mctx) <- quoteNondet mctx (l + 1) (b $ VVar l)
      pure (Sigma x a b, mctx)
    VPair t u -> do
      (t, mctx) <- quoteNondet mctx l t
      (u, mctx) <- quoteNondet mctx l u
      pure (Pair t u, mctx)
    VBrave {} -> []

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
  pretty ((mctx, l) :⊢ v) = pretty $ quote mctx l v

instance Pretty ((MetaCtx, [Name]) ⊢ Value) where
  pretty ((mctx, ns) :⊢ v) = pretty (ns :⊢ quote mctx (Level $ length ns) v)

instance Pretty ((MetaCtx, Level) ⊢ Unqualified Value) where
  pretty ((mctx, l) :⊢ Unqualified v) = pretty $ Unqualified (quote mctx l v)

instance Pretty ((MetaCtx, [Name]) ⊢ Unqualified Value) where
  pretty ((mctx, ns) :⊢ Unqualified v) =
    pretty (ns :⊢ Unqualified (quote mctx (Level $ length ns) v))
