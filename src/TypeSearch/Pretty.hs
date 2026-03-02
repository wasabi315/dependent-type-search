module TypeSearch.Pretty
  ( -- * Pretty printing
    prettyModule,
    prettyDecl,
    prettyRaw,
    prettyTerm,
    prettyIso,
  )
where

import Data.List (intersperse)
import Data.Monoid
import TypeSearch.Common
import TypeSearch.Raw as Raw
import TypeSearch.Term as Term

--------------------------------------------------------------------------------
-- Pretty printing

par :: Int -> Int -> ShowS -> ShowS
par p q = showParen (p > q)
{-# INLINE par #-}

punctuate :: ShowS -> [ShowS] -> ShowS
punctuate sep xs = foldr (.) id (intersperse sep xs)
{-# INLINE punctuate #-}

enclose :: ShowS -> ShowS -> ShowS -> ShowS
enclose open close x = open . x . close
{-# INLINE enclose #-}

-- Operator precedence
projP, appP, sigmaP, piP, absP, pairP :: Int
projP = 5
appP = 4
sigmaP = 3
piP = 2
absP = 1
pairP = 0

prettyModule :: Module -> ShowS
prettyModule (Module name imports decls) =
  showString "module "
    . shows name
    . showString " where"
    . showString "\n\n"
    . appEndo (foldMap (\m -> Endo $ showString "import " . shows m . showChar '\n') imports)
    . showChar '\n'
    . appEndo (foldMap (\d -> Endo $ prettyDecl d . showString "\n\n") decls)

prettyDecl :: Decl -> ShowS
prettyDecl = \case
  DLet _ n t u ->
    showString "let "
      . shows n
      . showString " : "
      . prettyRaw pairP t
      . showString " = "
      . prettyRaw pairP u
  DAxiom _ n t ->
    showString "postulate "
      . shows n
      . showString " : "
      . prettyRaw pairP t

prettyRaw :: Int -> Raw -> ShowS
prettyRaw = go
  where
    go p = \case
      RVar n -> shows n
      RMeta m -> shows m
      RU -> showString "U"
      RPi "_" a b -> par p piP $ go sigmaP a . showString " → " . go piP b
      RPi n a b -> par p piP $ piBind n a . goPi b
      RLam n b -> par p absP $ showString "λ " . shows n . goAbs b
      RApp a b -> par p appP $ go appP a . showChar ' ' . go projP b
      RSigma "_" a b -> par p piP $ go appP a . showString " × " . go sigmaP b
      RSigma n a b -> par p sigmaP $ piBind n a . showString " × " . go sigmaP b
      RPair a b -> par p pairP $ go absP a . showString " , " . go absP b
      RFst a -> par p projP $ go projP a . showString ".1"
      RSnd a -> par p projP $ go projP a . showString ".2"
      RPos t _ -> go p t

    piBind n a =
      showString "("
        . shows n
        . showString " : "
        . go pairP a
        . showChar ')'

    goPi = \case
      RPi "_" a b ->
        showString " → " . go sigmaP a . showString " → " . go piP b
      RPi n a b ->
        showChar ' ' . piBind n a . goPi b
      RPos t _ -> goPi t
      b -> showString " → " . go piP b

    goAbs = \case
      RLam n t -> showChar ' ' . shows n . goAbs t
      RPos t _ -> goAbs t
      t -> showString " → " . go absP t

prettyTerm :: [Name] -> Int -> Term -> ShowS
prettyTerm = go
  where
    go ns p = \case
      Var (Index i) -> shows (ns !! i)
      Meta m -> shows m
      Top n _ -> shows n
      U -> showString "U"
      Pi "_" a b ->
        par p piP $ go ns sigmaP a . showString " → " . go ("_" : ns) piP b
      Pi (freshen ns -> n) a b ->
        par p piP $ piBind n ns a . goPi (n : ns) b
      Lam (freshen ns -> n) t ->
        par p absP $
          showString "λ " . shows n . goAbs (n : ns) t
      App t u -> par p appP $ go ns appP t . showChar ' ' . go ns projP u
      AppPruning t pr -> goPruning (go ns appP t) ns pr
      Sigma "_" a b ->
        par p sigmaP $ go ns appP a . showString " × " . go ("_" : ns) sigmaP b
      Sigma (freshen ns -> n) a b ->
        par p sigmaP $ piBind n ns a . showString " × " . go (n : ns) sigmaP b
      Fst t -> par p projP $ go ns projP t . showString ".1"
      Snd t -> par p projP $ go ns projP t . showString ".2"
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
      _ _ -> error "impossible"

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
