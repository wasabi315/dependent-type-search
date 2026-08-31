module Aegle.Index.TransparentDefs
  ( decideTransparency,
    TransparentDefPolicy (..),
    OpaqueDefNames,
    OpaqueReason (..),
  )
where

import Aegle.Prelude
import Agda.Compiler.Backend hiding (None)
import Agda.Compiler.Common
import Agda.Syntax.Common hiding (PatternMatching)
import Agda.Syntax.Common.Pretty qualified as P
import Agda.Syntax.Internal
import Agda.TypeChecking.ProjectionLike
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute hiding (sort)
import Agda.TypeChecking.Telescope
import Agda.Utils.Impossible
import Agda.Utils.Monad (unlessM)
import Data.List.NonEmpty qualified as NE
import Data.Set qualified as S
import Data.Text qualified as T

--------------------------------------------------------------------------------
-- Transparent definition criteria

data TransparentDefPolicy
  = None
  | AllExcept OpaqueDefNames
  deriving stock (Eq, Ord, Show, Generic)

type OpaqueDefNames = S.Set T.Text

data OpaqueReason
  = NotFunction
  | ProjectionLike
  | HasLocalDefs (NE.NonEmpty QName)
  | PatternMatching
  | NoReturnSort
  | ExcludedByConfig
  deriving stock (Eq, Ord, Show, Generic)

decideTransparency :: OpaqueDefNames -> Definition -> TCM (Either OpaqueReason ())
decideTransparency opaques def = runExceptT do
  when (T.pack (P.prettyShow def.defName) `S.member` opaques) do
    throwError ExcludedByConfig

  fun <- case def.theDef of
    FunctionDefn fun -> pure fun
    _ -> throwError NotFunction

  locals <- lift $ localDefNames def.defName
  traverse_ (throwError . HasLocalDefs) (NE.nonEmpty locals)

  -- TODO: translate projection-like
  when (isProjectionLike fun) do
    throwError ProjectionLike

  when (isPatternMatching fun) do
    throwError PatternMatching

  -- Is this criterial really needed?
  unlessM (lift $ mayReturnSort def.defType) do
    throwError NoReturnSort

localDefNames :: QName -> TCM [QName]
localDefNames defName = do
  defs <- curDefs
  sortDefs defs
    & map fst
    & dropWhile (<= defName)
    & takeWhile (isAnonymousModuleName . qnameModule)
    & pure

isProjectionLike :: FunctionData -> Bool
isProjectionLike FunctionData {..} = isRight _funProjection

isPatternMatching :: FunctionData -> Bool
isPatternMatching FunctionData {..} =
  case _funClauses of
    [Clause {..}] ->
      isNothing clauseBody || flip any namedClausePats \pat -> case namedArg pat of
        VarP {} -> False
        _ -> True
    _ -> True

-- | Check whether a closed type **may** return 'Sort' if instantiated appropriately.
-- Does not consider large eliminations and universe levels.
mayReturnSort :: Type -> TCM Bool
mayReturnSort typ = do
  TelV tel b <- telView typ
  addContext tel do
    reduce b.unEl >>= elimView ButLone >>= \case
      Sort {}; Var {} -> pure True
      Def {}; DontCare {}; Dummy {} -> pure False
      -- Not a type
      Lam {}; Lit {}; Con {}; Level {} -> __IMPOSSIBLE__
      -- Can't occur after 'telView'
      Pi {} -> __IMPOSSIBLE__
      -- Assume no meta
      MetaV {} -> __IMPOSSIBLE__
