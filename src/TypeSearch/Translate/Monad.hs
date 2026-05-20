module TypeSearch.Translate.Monad
  ( Transl,
    runTransl,
    translateError,
    addContextAndRenaming,
    translateDBVar,
    isTransparentDef,
    locallyReduceTransparentDef,
    reduceTransparentDef,
    isErasable,
  )
where

import Agda.Compiler.Backend hiding (Args, initEnv)
import Agda.Syntax.Common
import Agda.Syntax.Internal hiding (arity, termSize)
import Agda.TypeChecking.Level
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute as Agda
import Agda.TypeChecking.Telescope
import Agda.Utils.Impossible (__IMPOSSIBLE__)
import Agda.Utils.Monad
import Data.IntMap qualified as IM
import Data.Set qualified as S
import TypeSearch.Core.Name qualified as TS
import TypeSearch.Prelude

--------------------------------------------------------------------------------
-- Monad for translation

type Transl = ReaderT TransEnv TCM

data TransEnv = TransEnv
  { -- | Context size after erasure
    contextSizeAfterErasure :: Int,
    -- | De Bruijn level → De Bruijn level after erasure
    renaming :: IM.IntMap Int,
    -- | Set of transparent definitions (already resolved)
    transparentDefNames :: S.Set QName,
    -- | Should transparent definitions be expanded?
    reduceTransparentDef :: Bool
  }

runTransl :: S.Set QName -> Transl a -> TCM a
runTransl = flip runReaderT . initEnv

initEnv :: S.Set QName -> TransEnv
initEnv transparentDefNames =
  TransEnv
    { contextSizeAfterErasure = 0,
      renaming = mempty,
      transparentDefNames,
      reduceTransparentDef = False
    }

--------------------------------------------------------------------------------
-- Transl interface

translateError :: (HasCallStack) => Transl Doc -> Transl a
translateError msg = typeError . CustomBackendError "translation" =<< msg

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

isTransparentDef :: QName -> Transl Bool
isTransparentDef x = asks \env -> x `S.member` env.transparentDefNames

locallyReduceTransparentDef :: Transl a -> Transl a
locallyReduceTransparentDef = local \env -> env {reduceTransparentDef = True}

reduceTransparentDef :: Term -> Transl Term
reduceTransparentDef t =
  ifNotM (asks \env -> env.reduceTransparentDef) (pure t) do
    ds <- asks \env -> OnlyReduceDefs env.transparentDefNames
    locallyReduceDefs ds $ reduce t

--------------------------------------------------------------------------------
-- Erase level/size

-- | Determine whether it is ok to erase arguments of this type.
isErasable :: Type -> Transl Bool
isErasable a = do
  TelV tel b <- telView a
  addContext tel $
    orM
      [ isLevelType b,
        isJust <$> isSizeType b
      ]
