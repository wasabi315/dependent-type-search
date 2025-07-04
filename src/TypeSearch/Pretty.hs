module TypeSearch.Pretty
  ( -- * Pretty printing
    prettyModule,
    prettyDecl,
    prettyRaw,
    prettyTerm,
    prettyMetaSubst,
    prettyInst,
  )
where

import Data.Function
import Data.HashMap.Strict qualified as HM
import Data.Monoid
import Data.Text qualified as T
import TypeSearch.Common
import TypeSearch.Raw
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

prettyModule :: Module -> ShowS
prettyModule (Module name imports decls) =
  showString "module "
    . shows name
    . showString " where"
    . showString "\n"
    . appEndo (foldMap (\m -> Endo $ showString "import " . shows m . showChar '\n') imports)
    . showChar '\n'
    . appEndo (foldMap (\d -> Endo $ prettyDecl d . showChar '\n') decls)

prettyDecl :: Decl -> ShowS
prettyDecl = \case
  DLet _ n t u ->
    showString "let "
      . shows n
      . showString " : "
      . prettyRaw pairP t
      . showString " = "
      . prettyRaw pairP u

prettyRaw :: Int -> Raw -> ShowS
prettyRaw = go
  where
    go p = \case
      RVar n -> shows n
      RMetaApp m [] -> shows m
      RMetaApp m ts ->
        shows m . showChar '[' . punctuate (showChar ',') (map (go absP) ts) . showChar ']'
      RType -> showString "Type"
      RUnit -> showString "Unit"
      RTT -> showString "tt"
      RPi n a b -> par p piP $ piBind n a . goPi b
      RArr a b -> par p piP $ go sigmaP a . showString " → " . go piP b
      RAbs n b -> par p absP $ showString "λ " . shows n . goAbs b
      RApp RSuc n -> goSuc p 1 n
      RApp a b -> par p appP $ go appP a . showChar ' ' . go projP b
      RSigma n a b -> par p sigmaP $ piBind n a . showString " × " . go sigmaP b
      RProd a b -> par p sigmaP $ go appP a . showString " × " . go sigmaP b
      RPair a b -> par p pairP $ go absP a . showString ", " . go absP b
      RFst a -> par p projP $ go projP a . showString ".1"
      RSnd a -> par p projP $ go projP a . showString ".2"
      RNat -> showString "Nat"
      RZero -> showString "0"
      RSuc -> showString "suc"
      RNatElim -> showString "natElim"
      REq -> showString "Eq"
      RRefl -> showString "refl"
      REqElim -> showString "eqElim"
      RPos t _ -> go p t

    goSuc p n = \case
      RZero -> shows n
      RSuc `RApp` m -> goSuc p (n + 1) m
      t -> applyN n (\f q -> par q appP $ showString "suc " . f projP) (\q -> go q t) p

    piBind n a =
      showString "("
        . shows n
        . showString " : "
        . go pairP a
        . showChar ')'

    goPi = \case
      (unRPos -> RPi n a b) ->
        showChar ' ' . piBind n a . goPi b
      b -> showString " → " . go piP b

    goAbs = \case
      (unRPos -> RAbs n t) -> showChar ' ' . shows n . goAbs t
      t -> showString " → " . go absP t

prettyTerm :: [Name] -> Int -> Term -> ShowS
prettyTerm = go
  where
    go ns p = \case
      Var (Index i) -> shows (ns !! i)
      MetaApp m [] -> shows m
      MetaApp m ts ->
        shows m . showChar '[' . punctuate (showChar ',') (map (go ns absP) ts) . showChar ']'
      Top _ n -> shows n
      Type -> showString "Type"
      Pi (freshen ns -> n) a b ->
        par p piP $ piBind n ns a . goPi (n : ns) b
      Arr a b -> par p piP $ go ns sigmaP a . showString " → " . go ns piP b
      Abs (freshen ns -> n) t ->
        par p absP $
          showString "λ " . shows n . goAbs (n : ns) t
      Suc `App` n -> goSuc p ns 1 n
      App t u -> par p appP $ go ns appP t . showChar ' ' . go ns projP u
      Sigma (freshen ns -> n) a b ->
        par p sigmaP $ piBind n ns a . showString " × " . go (n : ns) sigmaP b
      Prod a b -> par p sigmaP $ go ns appP a . showString " × " . go ns sigmaP b
      Fst t -> par p projP $ go ns projP t . showString ".1"
      Snd t -> par p projP $ go ns projP t . showString ".2"
      Pair t u -> par p pairP $ go ns absP t . showString ", " . go ns pairP u
      Unit -> showString "Unit"
      TT -> showString "tt"
      Nat -> showString "Nat"
      Zero -> showString "0"
      Suc -> showString "suc"
      NatElim -> showString "natElim"
      Eq -> showString "Eq"
      Refl -> showString "refl"
      EqElim -> showString "eqElim"

    goSuc p ns n = \case
      Zero -> shows n
      Suc `App` m -> goSuc p ns (n + 1) m
      t -> applyN n (\f q -> par q appP $ showString "suc " . f projP) (\q -> go ns q t) p

    piBind n ns a =
      showString "("
        . shows n
        . showString " : "
        . go ns pairP a
        . showChar ')'

    goPi ns = \case
      Pi (freshen ns -> n) a b ->
        showChar ' ' . piBind n ns a . goPi (n : ns) b
      b -> showString " → " . go ns piP b

    goAbs ns = \case
      Abs (freshen ns -> n) t ->
        showChar ' ' . shows n . goAbs (n : ns) t
      t -> showString ". " . go ns absP t

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

prettyMetaSubst :: MetaSubst -> ShowS
prettyMetaSubst = \subst ->
  HM.toList subst
    & map (uncurry prettyMetaAbs)
    & punctuate (showString ", ")
    & enclose (showChar '{') (showChar '}')
  where
    prettyMetaAbs m (MetaAbs arity body) =
      shows m
        . ( if arity > 0
              then
                showChar '['
                  . punctuate (showChar ',') (map shows params)
                  . showString "]"
              else id
          )
        . showString " ↦ "
        . prettyTerm (reverse params) absP body
      where
        params = map (\i -> Name $ "x" <> T.map subscript (T.pack (show i))) [0 .. arity - 1]

prettyInst :: [Name] -> HM.HashMap Name Term -> ShowS
prettyInst ns = \subst ->
  HM.toList subst
    & map (uncurry prettyBody)
    & punctuate (showString ", ")
    & enclose (showChar '{') (showChar '}')
  where
    prettyBody m t =
      shows m
        . showString " ↦ "
        . prettyTerm ns absP t
