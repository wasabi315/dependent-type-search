module TypeSearch.Database.Index.Common where

import Agda.Compiler.Backend hiding (Args, initEnv)
import Agda.Syntax.Common
import Agda.Syntax.Internal hiding (arity, termSize)
import Agda.TypeChecking.Level
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Sort
import Agda.TypeChecking.Substitute as Agda
import Agda.TypeChecking.Telescope
import Agda.Utils.CallStack (HasCallStack)
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Monad
import Control.Monad.Reader
import Data.HashSet qualified as HS
import Data.IntMap qualified as IM
import Data.Maybe
import Database.PostgreSQL.Simple
import TypeSearch.Common qualified as TS
import TypeSearch.Database.Common qualified as TS
import TypeSearch.Term qualified as TS

--------------------------------------------------------------------------------
-- Types

data IndexEnv = IndexEnv
  { maxLetSize :: Int,
    -- | Context size after erasure
    contextSizeAfterErasure :: Int,
    -- | De Bruijn level → De Bruijn level after erasure
    renaming :: IM.IntMap Int
  }

-- | Index monad.
type M = ReaderT IndexEnv TCM

data IndexConfig = IndexConfig
  { -- | Maximum Raw node count for a let-body; larger bodies fall back to DAxiom.
    maxLetSize :: Int,
    -- | Path to Agda library.
    libraryDirectory :: FilePath,
    -- | Connection to database.
    databaseConnection :: Connection
  }

initEnv :: IndexConfig -> IndexEnv
initEnv IndexConfig {..} = IndexEnv maxLetSize 0 mempty

data Item = Item
  { name :: TS.QName,
    signature :: TS.Term,
    body :: Maybe TS.Term,
    feature :: (TS.ReturnTypeHead, TS.Polymorphic, TS.Arity)
  }

--------------------------------------------------------------------------------
-- Utils

translateError :: (HasCallStack, MonadTCError m) => m Doc -> m a
translateError msg = typeError . CustomBackendError "dependent-type-search" =<< msg

-- | Extend both Agda's and our context and save the de Bruijn level association.
addContextAndRenaming :: (AddContext (name, Dom Type)) => (name, Dom Type) -> M a -> M a
addContextAndRenaming ctxElt m = do
  ctxSize <- getContextSize
  local
    ( \env ->
        env
          { contextSizeAfterErasure = env.contextSizeAfterErasure + 1,
            renaming = IM.insert ctxSize env.contextSizeAfterErasure env.renaming
          }
    )
    $ addContext ctxElt m

-- | Translate a de Bruijn index from Agda into ours according to the current renaming.
translateDBVar :: Nat -> M TS.Index
translateDBVar ix = do
  ctxSize <- getContextSize
  let lvl = ctxSize - ix - 1
  asks \env -> do
    let lvl' = IM.findWithDefault __IMPOSSIBLE__ lvl env.renaming
        ix' = env.contextSizeAfterErasure - lvl' - 1
    TS.Index ix'

-- | Determine whether it is ok to erase arguments of this type.
isErasable :: Type -> M Bool
isErasable a = do
  TelV tel b <- telView a
  addContext tel $
    orM
      [ isLevelType b,
        isJust <$> isSizeType b
      ]

--------------------------------------------------------------------------------
-- Agda utils

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
