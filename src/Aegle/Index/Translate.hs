module Aegle.Index.Translate
  ( Transl,
    Config (..),
    runTransl,
    addContextAndRenaming,
    translateDBVar,
    withAllDefsOpaque,
    isTransparentDef,
    reduceTransparentDef,
    lookupModuleOrigin,
    isErasable,
  )
where

import Aegle.Core.Name qualified as TS
import Aegle.Prelude
import Agda.Compiler.Backend hiding (Args, initEnv, topLevelModuleName)
import Agda.Interaction.Library.Base
import Agda.Syntax.Common
import Agda.Syntax.Internal hiding (arity, termSize)
import Agda.TypeChecking.Level
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute as Agda
import Agda.TypeChecking.Telescope
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Monad
import Data.IntMap qualified as IM
import Data.Set qualified as S

--------------------------------------------------------------------------------
-- Monad for translation

type Transl = ReaderT Env TCM

data Env = Env
  { -- | Context size after erasure. See 'isErasable' for what is erased.
    contextSizeAfterErasure :: Int,
    -- | De Bruijn level → De Bruijn level after erasure
    renaming :: IM.IntMap Int,
    -- | Set of transparent definitions (already resolved)
    transparentDefs :: S.Set QName,
    -- | Module origins
    moduleOrigins :: [(ModuleName, LibName)]
  }

data Config = Config
  { -- | Set of transparent definitions (already resolved)
    transparentDefs :: S.Set QName,
    -- | Module origins
    moduleOrigins :: [(ModuleName, LibName)]
  }

runTransl :: Config -> Transl a -> TCM a
runTransl Config {..} m =
  runReaderT m
    $ Env
      { contextSizeAfterErasure = 0,
        renaming = mempty,
        ..
      }

--------------------------------------------------------------------------------
-- Transl interface

-- | Extend both Agda's and our context and save the de Bruijn level association.
addContextAndRenaming :: (AddContext (name, Dom Type)) => (name, Dom Type) -> Transl a -> Transl a
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
translateDBVar :: Nat -> Transl TS.Index
translateDBVar ix = do
  ctxSize <- getContextSize
  asks \env -> do
    let lvl = ctxSize - ix - 1
        lvl' = IM.findWithDefault __IMPOSSIBLE__ lvl env.renaming
        ix' = env.contextSizeAfterErasure - lvl' - 1
    TS.Index ix'

withAllDefsOpaque :: Transl a -> Transl a
withAllDefsOpaque = local \Env {..} -> Env {transparentDefs = mempty, ..}

isTransparentDef :: QName -> Transl Bool
isTransparentDef x = asks \env -> x `S.member` env.transparentDefs

reduceTransparentDef :: Term -> Transl Term
reduceTransparentDef t = do
  ds <- asks \env -> OnlyReduceDefs env.transparentDefs
  locallyReduceDefs ds $ reduce t

lookupModuleOrigin :: ModuleName -> Transl LibName
lookupModuleOrigin m = asks \env ->
  maybe (impossible "lookupModuleOrigin") snd do
    find
      (\(m', _) -> m' `isLeParentModuleOf` m)
      env.moduleOrigins

--------------------------------------------------------------------------------
-- Erase level/size

-- | Determine whether it is ok to erase arguments of this type.
isErasable :: Type -> Transl Bool
isErasable a = do
  TelV tel b <- telView a
  addContext tel
    $ orM
      [ isLevelType b,
        isJust <$> isSizeType b
      ]
