module TypeSearch.Database.Query
  ( Term (..),
    Type,
    teleView,
    endsInSort,
    appView,
    headTerm,
    returnType,
    freeVars,
    possibleResolutions,
  )
where

import Data.Map.Strict qualified as M
import Data.Set qualified as S
import TypeSearch.Core.Name
import TypeSearch.Core.Term (AppView (..), TeleView (..))
import TypeSearch.Core.Term qualified as C
import TypeSearch.Prelude

--------------------------------------------------------------------------------

-- | Query term
data Term
  = Var PQName
  | U
  | Pi Name Term Term
  | Lam Name Term
  | App Term Term
  | Sigma Name Term Term
  | Pair Term Term
  | Proj1 Term
  | Proj2 Term
  deriving stock (Show)

type Type = Term

--------------------------------------------------------------------------------

teleView :: Term -> TeleView Term
teleView = go []
  where
    go tele = \case
      Pi x a b -> go ((x, a) : tele) b
      cod -> TeleView tele cod

-- | Get the return type. Doesn't perform any reduction.
returnType :: Term -> Term
returnType = (.cod) . teleView

-- | Is the return type U? Doesn't perform any reduction.
endsInSort :: Term -> Bool
endsInSort t = case returnType t of
  U -> True
  _ -> False

appView :: Term -> AppView Term
appView = go id
  where
    go args = \case
      App t u -> go ((u :) . args) t
      t -> AppView {head = t, args = args []}

-- | The head term. Doesn't consider projections as elimination. Doesn't perform any reduction.
headTerm :: Term -> Term
headTerm = (.head) . appView

freeVars :: Term -> S.Set PQName
freeVars = \case
  Var x -> S.singleton x
  U -> S.empty
  Pi x a b -> S.delete (Unqual x) $ freeVars a <> freeVars b
  Lam x t -> S.delete (Unqual x) $ freeVars t
  App t u -> freeVars t <> freeVars u
  Sigma x a b -> S.delete (Unqual x) $ freeVars a <> freeVars b
  Pair t u -> freeVars t <> freeVars u
  Proj1 t -> freeVars t
  Proj2 t -> freeVars t

possibleResolutions :: M.Map Name [QName] -> Term -> [C.Term]
possibleResolutions tbl = flip evalStateT mempty . go []
  where
    fixName qn = StateT \fixed -> do
      fixed <-
        M.alterF
          ( maybe
              (pure $ Just qn)
              \qn' -> if qn == qn' then pure (Just qn) else []
          )
          qn.name
          fixed
      pure ((), fixed)

    go ns = \case
      Var (Unqual x)
        | Just i <- x `elemIndex` ns -> pure $ C.Var (Index i)
      Var (Unqual x) -> do
        qn <- lift $ fromMaybe [] (tbl M.!? x)
        fixName qn
        pure $ C.Top qn
      Var (Qual m x) -> do
        fixName (QName m x)
        pure $ C.Top (QName m x)
      U -> pure C.U
      Pi x a b -> C.Pi x <$> go ns a <*> go (x : ns) b
      Lam x t -> C.Lam x <$> go (x : ns) t
      App t u -> C.App <$> go ns t <*> go ns u
      Sigma x a b -> C.Sigma x <$> go ns a <*> go (x : ns) b
      Pair t u -> C.Pair <$> go ns t <*> go ns u
      Proj1 t -> C.Proj1 <$> go ns t
      Proj2 t -> C.Proj2 <$> go ns t
