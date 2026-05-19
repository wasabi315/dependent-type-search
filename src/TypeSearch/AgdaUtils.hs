module TypeSearch.AgdaUtils
  ( module TypeSearch.AgdaUtils,
  )
where

import Agda.Compiler.Backend hiding (Args, initEnv)
import Agda.Interaction.BasicOps
import Agda.Syntax.Common
import Agda.Syntax.Internal hiding (arity, termSize)
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Sort
import Agda.TypeChecking.Substitute as Agda
import Agda.TypeChecking.Telescope
import Data.Map.Strict qualified as M
import Data.Text qualified as T
import TypeSearch.Prelude

--------------------------------------------------------------------------------

setCurrentRangeQ :: (MonadTrace m) => QName -> m a -> m a
setCurrentRangeQ = setCurrentRange . nameBindingSite . qnameName

-- | Try to unfold a definition if introduced by module application.
maybeUnfoldCopy ::
  (PureTCM m) =>
  -- | Name of the definition.
  QName ->
  Elims ->
  -- | Callback if the definition is indeed a copy.
  (Term -> m a) ->
  -- | Callback if the definition isn't a copy.
  (QName -> Elims -> m a) ->
  m a
maybeUnfoldCopy f es onTerm onDef =
  reduceDefCopy f es >>= \case
    NoReduction () -> onDef f es
    YesReduction _ t -> onTerm t

-- | Check if a type returns Sort
endsInSort :: (PureTCM m, MonadBlock m) => Type -> m Bool
endsInSort t = do
  TelV tel b <- telView t
  addContext tel $ ifIsSort b (\_ -> return True) (return False)

realName :: ArgName -> String
realName s = if isNoName s then "x" else argNameToString s

isDeprecated :: (ReadTCState m) => QName -> m Bool
isDeprecated x = do
  ws <- getUserWarnings
  case M.lookup x ws of
    Nothing -> pure False
    Just txt -> pure $! T.toCaseFold "deprecated" `T.isInfixOf` T.toCaseFold txt

resolveDefinedName :: (MonadTCM m) => String -> m (Maybe QName)
resolveDefinedName s = do
  rname <- liftTCM $ resolveName =<< parseName noRange s
  case rname of
    DefinedName _ aname _ -> pure $ Just $ anameName aname
    _ -> pure Nothing
