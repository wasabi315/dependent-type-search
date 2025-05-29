module TypeSearch.Pretty
  ( -- * Pretty printing
    prettyTerm,
    prettyMetaSubst,
  )
where

import Data.Function
import Data.HashMap.Strict qualified as HM
import Data.Text qualified as T
import TypeSearch.Common
import TypeSearch.Term

--------------------------------------------------------------------------------
-- Pretty printing

-- Operator precedence
projP, appP, sigmaP, piP, absP, pairP :: Int
projP = 5
appP = 4
sigmaP = 3
piP = 2
absP = 1
pairP = 0

prettyTerm :: [Name] -> Int -> Term -> ShowS
prettyTerm = go
  where
    go ns p = \case
      Var (Index i) -> showString $ T.unpack (ns !! i)
      MetaApp m ts ->
        shows m . showChar '[' . punctuate (showChar ',') (map (go ns absP) ts) . showChar ']'
      Top n -> shows n
      Type -> showString "Type"
      Unit -> showString "Unit"
      TT -> showString "tt"
      Pi "_" a b ->
        par p piP $
          go ns sigmaP a . showString " → " . go ("_" : ns) piP b
      Pi (freshen ns -> n) a b ->
        par p piP $ piBind n ns a . goPi (n : ns) b
      Abs (freshen ns -> n) t ->
        par p absP $
          showString "λ " . showString (T.unpack n) . goAbs (n : ns) t
      App t u -> par p appP $ go ns appP t . showChar ' ' . go ns projP u
      Sigma (freshen ns -> n) a b ->
        par p sigmaP $
          showString "Σ "
            . showString (T.unpack n)
            . showString " : "
            . go ns appP a
            . showString ". "
            . go (n : ns) sigmaP b
      Fst t -> par p projP $ go ns projP t . showString ".1"
      Snd t -> par p projP $ go ns projP t . showString ".2"
      Pair t u -> par p pairP $ go ns absP t . showString ", " . go ns pairP u

    piBind n ns a =
      showString "("
        . showString (T.unpack n)
        . showString " : "
        . go ns pairP a
        . showChar ')'

    goPi ns = \case
      Pi "_" a b ->
        showString " → " . go ns sigmaP a . showString " → " . go ("_" : ns) piP b
      Pi (freshen ns -> n) a b ->
        showChar ' ' . piBind n ns a . goPi (n : ns) b
      b -> showString " → " . go ns piP b

    goAbs ns = \case
      Abs (freshen ns -> n) t ->
        showChar ' ' . showString (T.unpack n) . go (n : ns) absP t
      t -> showString ". " . go ns absP t

prettyMetaSubst :: MetaSubst -> ShowS
prettyMetaSubst = \subst ->
  HM.toList subst
    & map (uncurry prettyMetaAbs)
    & punctuate (showString ", ")
    & enclose (showChar '{') (showChar '}')
  where
    prettyMetaAbs m (MetaAbs arity body) =
      shows m
        . showChar '['
        . punctuate (showChar ',') (map showString params)
        . showString "] ↦ "
        . prettyTerm (reverse (map T.pack params)) absP body
      where
        params = map (\i -> "x" <> show i) [0 .. arity - 1]
