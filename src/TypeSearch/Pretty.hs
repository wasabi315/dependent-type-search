module TypeSearch.Pretty
  ( -- * Pretty printing
    prettyTerm,
    prettyTerm0,
    prettyIso,
    prettyQuery,
    QualifyMode (..),
  )
where

import Data.Text qualified as T
import TypeSearch.Core.Isomorphism
import TypeSearch.Core.Name
import TypeSearch.Core.Term
import TypeSearch.Database.Query qualified as Q
import TypeSearch.Prelude

--------------------------------------------------------------------------------
-- Pretty printing

par :: Int -> Int -> ShowS -> ShowS
par p q = showParen (p > q)
{-# INLINE par #-}

-- Operator precedence
projP, appP, sigmaP, piP, absP, pairP :: Int
projP = 5
appP = 4
sigmaP = 3
piP = 2
absP = 1
pairP = 0

prettyQuery :: QualifyMode -> Int -> Q.Term -> ShowS
prettyQuery qm = go
  where
    go p = \case
      Q.Var (Unqual n) -> shows n
      Q.Var (Qual m n) -> case qm of
        Qualify -> shows (Qual m n)
        Unqualify -> shows n
      Q.U -> showString "U"
      Q.Pi "_" a b -> par p piP $ go sigmaP a . showString " → " . go piP b
      Q.Pi n a b -> par p piP $ piBind n a . goPi b
      Q.Lam n b -> par p absP $ showString "λ " . shows n . goAbs b
      Q.App a b -> par p appP $ go appP a . showChar ' ' . go projP b
      Q.Sigma "_" a b -> par p piP $ go appP a . showString " × " . go sigmaP b
      Q.Sigma n a b -> par p sigmaP $ piBind n a . showString " × " . go sigmaP b
      Q.Pair a b -> par p pairP $ go absP a . showString " , " . go absP b
      Q.Proj1 a -> par p projP $ go projP a . showString ".1"
      Q.Proj2 a -> par p projP $ go projP a . showString ".2"

    piBind n a =
      showString "("
        . shows n
        . showString " : "
        . go pairP a
        . showChar ')'

    goPi = \case
      Q.Pi "_" a b ->
        showString " → " . go sigmaP a . showString " → " . go piP b
      Q.Pi n a b ->
        showChar ' ' . piBind n a . goPi b
      b -> showString " → " . go piP b

    goAbs = \case
      Q.Lam n t -> showChar ' ' . shows n . goAbs t
      t -> showString " → " . go absP t

data QualifyMode = Qualify | Unqualify

prettyTerm0 :: QualifyMode -> Term -> ShowS
prettyTerm0 qm t = prettyTerm qm [] 0 t

prettyTerm :: QualifyMode -> [Name] -> Int -> Term -> ShowS
prettyTerm qm = go
  where
    go ns p = \case
      Var (Index i) -> shows (ns !! i)
      Meta m -> shows m
      Top n -> case qm of
        Qualify -> shows n
        Unqualify -> shows n.name
      U -> showString "U"
      Pi "_" a b ->
        par p piP $ go ns sigmaP a . showString " → " . go ("_" : ns) piP b
      Pi (freshen ns -> n) a b ->
        par p piP $ piBind n ns a . goPi (n : ns) b
      Lam (freshen ns -> n) t ->
        par p absP
          $ showString "λ "
          . shows n
          . goAbs (n : ns) t
      App t u -> par p appP $ go ns appP t . showChar ' ' . go ns projP u
      AppPruning t pr -> goPruning (go ns appP t) ns pr
      Sigma "_" a b ->
        par p sigmaP $ go ns appP a . showString " × " . go ("_" : ns) sigmaP b
      Sigma (freshen ns -> n) a b ->
        par p sigmaP $ piBind n ns a . showString " × " . go (n : ns) sigmaP b
      Proj1 t -> par p projP $ go ns projP t . showString ".1"
      Proj2 t -> par p projP $ go ns projP t . showString ".2"
      Pair t u -> par p pairP $ go ns absP t . showString " , " . go ns pairP u

    piBind n ns a =
      showString "("
        . shows n
        . showString " : "
        . go ns pairP a
        . showChar ')'

    goPi ns = \case
      Pi "_" a b -> showString " → " . go ns sigmaP a . showString " → " . go ("_" : ns) piP b
      Pi (freshen ns -> n) a b ->
        showChar ' ' . piBind n ns a . goPi (n : ns) b
      b -> showString " → " . go ns piP b

    goAbs ns = \case
      Lam (freshen ns -> n) t ->
        showChar ' ' . shows n . goAbs (n : ns) t
      t -> showString ". " . go ns absP t

    goPruning t = \cases
      [] [] -> t
      (n : ns) (True : pr) -> goPruning t ns pr . showChar ' ' . shows n
      (_ : ns) (False : pr) -> goPruning t ns pr
      _ _ -> impossible

prettyIso :: Int -> Iso -> ShowS
prettyIso p = \case
  Refl -> showString "refl"
  Sym i -> par p 11 $ prettyIso 12 i . showString " ⁻¹"
  Trans i j -> par p 9 $ prettyIso 9 i . showString " · " . prettyIso 9 j
  Assoc -> showString "Assoc"
  Comm -> showString "Comm"
  SigmaSwap -> showString "ΣSwap"
  Curry -> showString "Curry"
  PiSwap -> showString "ΠSwap"
  PiCongL i -> par p 10 $ showString "ΠL " . prettyIso 11 i
  PiCongR i -> par p 10 $ showString "ΠR " . prettyIso 11 i
  SigmaCongL i -> par p 10 $ showString "ΣL " . prettyIso 11 i
  SigmaCongR i -> par p 10 $ showString "ΣR " . prettyIso 11 i

freshen :: [Name] -> Name -> Name
freshen ns n
  | n `elem` ns = go 0
  | otherwise = n
  where
    go (i :: Int)
      | n' `notElem` ns = n'
      | otherwise = go (i + 1)
      where
        n' = Name $ coerce n <> T.pack (map subscript (show i))

subscript :: Char -> Char
subscript = \case
  '0' -> '₀'
  '1' -> '₁'
  '2' -> '₂'
  '3' -> '₃'
  '4' -> '₄'
  '5' -> '₅'
  '6' -> '₆'
  '7' -> '₇'
  '8' -> '₈'
  '9' -> '₉'
  c -> c
