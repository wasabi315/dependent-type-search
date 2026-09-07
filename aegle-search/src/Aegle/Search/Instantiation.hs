module Aegle.Search.Instantiation
  ( check0,
    check,
  )
where

import Aegle.Core.Isomorphism hiding (quoteIso, transport, transportInv)
import Aegle.Core.Name
import Aegle.Core.Term qualified as C
import Aegle.Prelude
import Aegle.Search.Evaluation
import Aegle.Search.Isomorphism
import Aegle.Search.Matching.ModuloIso
import Aegle.Search.Term
import Data.ImmatureStream qualified as IStr
import Prettyprinter

--------------------------------------------------------------------------------
-- Context

data Ctx = Ctx
  { level :: Level,
    locals :: Locals
  }

data Locals
  = Here
  | Bind Locals Name ~Term

initCtx :: Ctx
initCtx =
  Ctx
    { level = 0,
      locals = Here
    }

bind :: MetaCtx -> Ctx -> Name -> VType -> Ctx
bind mctx ctx@Ctx {..} x ~a =
  ctx
    { level = level + 1,
      locals = Bind locals x (quote mctx level a)
    }

--------------------------------------------------------------------------------

closeTy :: Locals -> Term -> Term
closeTy = \cases
  Here b -> b
  (Bind locs x a) b -> closeTy locs (Pi x a b)

closeTm :: Locals -> Term -> Term
closeTm = \cases
  Here t -> t
  (Bind locs x _) b -> closeTm locs (Lam x b)

check0 :: MetaCtx -> Value -> QName -> C.Type -> IStr.Stream (Iso, Term)
check0 mctx query itemName item = do
  let ctx = initCtx
      item' = evalCore [] item
  check mctx ctx query itemName item'

-- FIXME: currently not considering pi permutation
check :: MetaCtx -> Ctx -> Value -> QName -> Value -> IStr.Stream (Iso, Term)
check mctx ctx query itemName item | traceCheck mctx ctx query itemName item = undefined
check mctx ctx query itemName item =
  asum
    [ do
        (item, inst, mctx) <- possibleInstantiation mctx ctx item (VNe (HOpaque itemName) SNil)
        (i, mctx) <- IStr.maybeToStream $ listToMaybe do
          (i, i', mctx) <- matchIso mctx ctx.level ! #pat item ! #term query
          guard $ allMetaSolved mctx
          pure $! i <> sym i' // mctx
        let ~sol = closeTm ctx.locals $ quote mctx ctx.level $ transport i inst
        pure (i, sol),
      IStr.Later do
        (query, mctx) <- choose $ forceNondet mctx query
        case query of
          VPi "_" _ _ -> empty
          VPi x a b -> do
            check mctx (bind mctx ctx x a) (b $ VVar ctx.level) itemName item
          _ -> empty
    ]

-- FIXME: currently not considering pi permutation
possibleInstantiation :: MetaCtx -> Ctx -> Value -> Value -> IStr.Stream (Value, Value, MetaCtx)
possibleInstantiation mctx ctx a ~_ | tracePossibleInstantiation mctx ctx a = undefined
possibleInstantiation mctx ctx a ~inst =
  asum
    [ pure (a, inst, mctx),
      IStr.Later case force mctx a of
        VPi "_" _ _ -> empty
        VPi _ a b -> do
          (m, mctx) <- pure $ freshMeta mctx ctx a
          let mv = eval mctx (idEnv ctx.level) m
          possibleInstantiation mctx ctx (b mv) (inst $$ mv)
        _ -> empty
    ]

idPruning :: Level -> Pruning
idPruning l = replicate (coerce l) True

freshMeta :: MetaCtx -> Ctx -> Value -> (Term, MetaCtx)
freshMeta mctx ctx a = do
  let ~closed = eval mctx [] $ closeTy ctx.locals (quote mctx ctx.level a)
      (m, mctx') = newMeta mctx closed
  (AppPruning (Meta m) (idPruning ctx.level), mctx')

--------------------------------------------------------------------------------

traceCheck :: MetaCtx -> Ctx -> Value -> QName -> Value -> Bool
traceCheck mctx ctx query itemName item = traceFalse $ show do
  vsep
    [ "check" <+> pretty itemName,
      "mctx" <+> colon <+> align (pretty mctx),
      "ctx size" <+> colon <+> pretty ctx.level,
      "query" <+> colon <+> pretty ((mctx, ctx.level) :⊢ query),
      "item" <+> colon <+> pretty ((mctx, ctx.level) :⊢ item)
    ]

tracePossibleInstantiation :: MetaCtx -> Ctx -> Value -> Bool
tracePossibleInstantiation mctx ctx a = traceFalse $ show do
  vsep
    [ "possibleInstantiation",
      "mctx" <+> colon <+> align (pretty mctx),
      "a" <+> colon <+> pretty ((mctx, ctx.level) :⊢ a)
    ]
