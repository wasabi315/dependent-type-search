module TypeSearch.Term
  ( -- * Terms
    Term (..),
    MetaAbs (..),
    MetaSubst,
  )
where

import Data.HashMap.Strict qualified as HM
import TypeSearch.Common

--------------------------------------------------------------------------------

-- | Terms
data Term
  = Var Index -- x
  | MetaApp Meta [Term] -- M[t1, ..., tn]
  | Top [ModuleName] Name -- f
  | Type -- Type
  | Pi Name Term Term -- (x : A) -> B
  | Abs Name Term -- \x -> t
  | App Term Term -- t1 t2
  | Sigma Name Term Term -- (x : A) * B
  | Pair Term Term -- (t1, t2)
  | Fst Term -- fst t
  | Snd Term -- snd t
  | Unit -- Unit
  | TT -- tt
  | Nat -- Nat
  | Zero -- zero
  | Suc -- suc
  | NatElim -- natElim
  | Eq -- Eq
  | Refl -- refl
  | EqElim -- eqElim
  deriving stock (Show)

-- | Meta abstractions
data MetaAbs = MetaAbs
  { arity :: Int,
    body :: Term
  }
  deriving stock (Show)

type MetaSubst = HM.HashMap Meta MetaAbs
