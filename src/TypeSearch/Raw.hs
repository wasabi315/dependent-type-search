module TypeSearch.Raw
  ( -- * Modules
    Module (..),
    Decl (..),

    -- * Raw terms
    Raw (..),
    unRPos,
    RTeleView (..),
    rteleView,
    rawEndsInSort,
    rawHeadTerm,
    rawReturnType,
    rawFreeVars,
  )
where

import Data.Set qualified as S
import TypeSearch.Common

--------------------------------------------------------------------------------

data Module = Module
  { name :: ModuleName,
    imports :: [ModuleName],
    decls :: [Decl]
  }
  deriving stock (Show)

data Decl
  = DLet (Maybe SourcePos) PQName Raw Raw
  | DAxiom (Maybe SourcePos) PQName Raw
  deriving stock (Show)

-- | Raw terms
data Raw
  = RVar PQName
  | RU
  | RPi Name Raw Raw
  | RLam Name Raw
  | RApp Raw Raw
  | RSigma Name Raw Raw
  | RPair Raw Raw
  | RProj1 Raw
  | RProj2 Raw
  | RPos Raw SourcePos
  deriving stock (Show)

unRPos :: Raw -> Raw
unRPos = \case
  RPos t _ -> unRPos t
  t -> t

--------------------------------------------------------------------------------

data RTeleView = RTeleView
  { tele :: [(Name, Raw)],
    cod :: Raw
  }

rteleView :: Raw -> RTeleView
rteleView = go []
  where
    go tele t = case unRPos t of
      RPi x a b -> go ((x, a) : tele) b
      cod -> RTeleView tele cod

-- | Get the return type. Doesn't perform any reduction.
rawReturnType :: Raw -> Raw
rawReturnType = \case
  (unRPos -> RPi _ _ b) -> rawReturnType b
  t -> t

-- | Is the return type U? Doesn't perform any reduction.
rawEndsInSort :: Raw -> Bool
rawEndsInSort t = case unRPos (rawReturnType t) of
  RU -> True
  _ -> False

-- | The head term. Doesn't consider projections as elimination. Doesn't perform any reduction.
rawHeadTerm :: Raw -> Raw
rawHeadTerm = \case
  (unRPos -> RApp t _) -> rawHeadTerm t
  t -> t

rawFreeVars :: Raw -> S.Set PQName
rawFreeVars = \case
  RVar x -> S.singleton x
  RU -> S.empty
  RPi x a b -> S.delete (Unqual x) $ rawFreeVars a <> rawFreeVars b
  RLam x t -> S.delete (Unqual x) $ rawFreeVars t
  RApp t u -> rawFreeVars t <> rawFreeVars u
  RSigma x a b -> S.delete (Unqual x) $ rawFreeVars a <> rawFreeVars b
  RPair t u -> rawFreeVars t <> rawFreeVars u
  RProj1 t -> rawFreeVars t
  RProj2 t -> rawFreeVars t
  RPos t _ -> rawFreeVars t
