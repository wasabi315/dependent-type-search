module Aegle.Core.Evaluation
  ( Value (..),
    VType,
    Head (..),
    Spine (..),
    pattern VVar,
    VQuant (..),
    Env,
    pattern (:>),
    ($$),
    vProj1,
    vProj2,
    pattern (:*),
    eval,
    levelToIndex,
    quote,
    nf,
  )
where

import Aegle.Core.Name
import Aegle.Core.Term
import Aegle.Prelude
import Prettyprinter

infixr 4 :*

infixl 5 :>

--------------------------------------------------------------------------------

-- | Values
data Value
  = VNe Head Spine
  | VU
  | VPi Name VType (Value -> VType)
  | VLam Name (Value -> Value)
  | VSigma Name VType (Value -> VType)
  | VPair Value Value

type VType = Value

data Head
  = HRigid Level
  | HOpaque QName
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

pattern (:>) :: [a] -> a -> [a]
pattern e :> v <- v : e
  where
    e :> ~v = v : e

--------------------------------------------------------------------------------

($$) :: Value -> Value -> Value
t $$ u = case t of
  VLam _ t -> t u
  VNe h sp -> VNe h (SApp sp u)
  _ -> error "($$): not a function"

vProj1 :: Value -> Value
vProj1 = \case
  VPair t _ -> t
  VNe h sp -> VNe h (SProj1 sp)
  _ -> error "vProj1: not a pair"

vProj2 :: Value -> Value
vProj2 = \case
  VPair _ t -> t
  VNe h sp -> VNe h (SProj2 sp)
  _ -> error "vProj2: not a pair"

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
  _ -> error "vUnpair: not a pair"

pattern (:*) :: Value -> Value -> Value
pattern t :* u <- (vUnpair -> (t, u))
  where
    t :* u = VPair t u

{-# COMPLETE (:*) #-}

{-# INLINE (:*) #-}

--------------------------------------------------------------------------------
-- NbE

eval :: Env -> Term -> Value
eval env = \case
  Var (Index x) -> env !! x
  Opaque x -> VNe (HOpaque x) SNil
  U -> VU
  Pi x a b -> VPi x (eval env a) \ ~t -> eval (env :> t) b
  Lam x t -> VLam x \u -> eval (env :> u) t
  App t u -> eval env t $$ eval env u
  Sigma x a b -> VSigma x (eval env a) \ ~t -> eval (env :> t) b
  Pair t u -> VPair (eval env t) (eval env u)
  Proj1 t -> vProj1 (eval env t)
  Proj2 t -> vProj2 (eval env t)

quote :: Level -> Value -> Term
quote l = \case
  VNe h sp -> quoteSpine l (quoteHead l h) sp
  VU -> U
  VPi x a b -> Pi x (quote l a) (quote (l + 1) (b (VVar l)))
  VLam x t -> Lam x (quote (l + 1) (t (VVar l)))
  VSigma x a b -> Sigma x (quote l a) (quote (l + 1) (b (VVar l)))
  VPair t u -> Pair (quote l t) (quote l u)

quoteHead :: Level -> Head -> Term
quoteHead l = \case
  HRigid x -> Var (levelToIndex l x)
  HOpaque x -> Opaque x

quoteSpine :: Level -> Term -> Spine -> Term
quoteSpine l h = \case
  SNil -> h
  SApp sp u -> quoteSpine l h sp `App` quote l u
  SProj1 sp -> Proj1 $ quoteSpine l h sp
  SProj2 sp -> Proj2 $ quoteSpine l h sp

nf :: Env -> Term -> Term
nf env t = quote (Level $ length env) (eval env t)

--------------------------------------------------------------------------------

instance Pretty (Level ⊢ Value) where
  pretty (l :⊢ v) = pretty $ quote l v

instance Pretty ([Name] ⊢ Value) where
  pretty (ns :⊢ v) = pretty (ns :⊢ quote (Level $ length ns) v)

instance Pretty (Level ⊢ Unqualified Value) where
  pretty (l :⊢ Unqualified v) = pretty $ Unqualified (quote l v)

instance Pretty ([Name] ⊢ Unqualified Value) where
  pretty (ns :⊢ Unqualified v) =
    pretty (ns :⊢ Unqualified (quote (Level $ length ns) v))
