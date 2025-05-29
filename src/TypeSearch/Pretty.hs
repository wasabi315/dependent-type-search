module TypeSearch.Pretty
  ( -- * Pretty printing
    prettyModule,
    prettyDecl,
    prettyRaw,
    prettyTerm,
    prettyMetaSubst,
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
  DLet n t u ->
    showString "let "
      . shows n
      . showString " : "
      . prettyRaw pairP t
      . showString " = "
      . prettyRaw pairP u
  DLoc (d :@ _) -> prettyDecl d

prettyRaw :: Int -> Raw -> ShowS
prettyRaw = go
  where
    go p = \case
      RVar n -> shows n
      RMetaApp m ts ->
        shows m . showChar '[' . punctuate (showChar ',') (map (go absP) ts) . showChar ']'
      RType -> showString "Type"
      RUnit -> showString "Unit"
      RTT -> showString "tt"
      RPi "_" a b -> par p piP $ go sigmaP a . showString " → " . go piP b
      RPi n a b -> par p piP $ piBind n a . goPi b
      RAbs n b -> par p absP $ showString "λ " . shows n . goAbs b
      RApp a b -> par p appP $ go appP a . showChar ' ' . go projP b
      RSigma "_" a b -> par p sigmaP $ go appP a . showString " × " . go sigmaP b
      RSigma n a b ->
        par p sigmaP $
          showString "Σ "
            . shows n
            . showString " : "
            . go appP a
            . showString ". "
            . go sigmaP b
      RPair a b -> par p pairP $ go absP a . showString ", " . go absP b
      RFst a -> par p projP $ go projP a . showString ".1"
      RSnd a -> par p projP $ go projP a . showString ".2"
      RLoc (t :@ _) -> go p t

    piBind n a =
      showString "("
        . shows n
        . showString " : "
        . go pairP a
        . showChar ')'

    goPi = \case
      (unRLoc -> RPi "_" a b) ->
        showString " → " . go sigmaP a . showString " → " . go piP b
      (unRLoc -> RPi n a b) ->
        showChar ' ' . piBind n a . goPi b
      b -> showString " → " . go piP b

    goAbs = \case
      (unRLoc -> RAbs n t) -> showChar ' ' . shows n . goAbs t
      t -> showString " → " . go absP t

prettyTerm :: [Name] -> Int -> Term -> ShowS
prettyTerm = go
  where
    go ns p = \case
      Var (Index i) -> shows (ns !! i)
      MetaApp m ts ->
        shows m . showChar '[' . punctuate (showChar ',') (map (go ns absP) ts) . showChar ']'
      Top _ n -> shows n
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
          showString "λ " . shows n . goAbs (n : ns) t
      App t u -> par p appP $ go ns appP t . showChar ' ' . go ns projP u
      Sigma "_" a b ->
        par p sigmaP $
          go ns appP a . showString " × " . go ("_" : ns) sigmaP b
      Sigma (freshen ns -> n) a b ->
        par p sigmaP $
          showString "Σ "
            . shows n
            . showString " : "
            . go ns appP a
            . showString ". "
            . go (n : ns) sigmaP b
      Fst t -> par p projP $ go ns projP t . showString ".1"
      Snd t -> par p projP $ go ns projP t . showString ".2"
      Pair t u -> par p pairP $ go ns absP t . showString ", " . go ns pairP u

    piBind n ns a =
      showString "("
        . shows n
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
        showChar ' ' . shows n . goAbs (n : ns) t
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
        . punctuate (showChar ',') (map shows params)
        . showString "] ↦ "
        . prettyTerm (reverse params) absP body
      where
        params = map (\i -> Name $ "x" <> T.pack (show i)) [0 .. arity - 1]
