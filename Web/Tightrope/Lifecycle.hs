{-# LANGUAGE TypeApplications #-}
module Web.Tightrope.Lifecycle where

import Web.Tightrope.Types

import Control.Monad.IO.Class

import Data.Proxy

onCreate :: forall impl state algebra out
          . MonadDom impl (DomM impl)
         => (state -> algebra ()) -> Snippet' impl out state algebra
onCreate action = Snippet $ \run st _ pos ->
                  pure (ConstructedSnippet mempty (AfterAction [ const (liftDom (Proxy @impl) (run (action st))) ])
                                           pos pos emptySnippet (pure ()))

onFinish :: Monad (DomM impl)
         => (state -> DomM impl ()) -> Snippet' impl out state algebra
onFinish action = Snippet $ \run st _ pos ->
                  pure (ConstructedSnippet mempty mempty pos pos (onFinish action) (action st))

afterDraw :: forall impl state out algebra
           . Monad (DomM impl)
          => (RunAlgebra impl algebra -> state -> out -> DomM impl ())
          -> Snippet' impl out state algebra
afterDraw action =
    Snippet $ \run st _ pos ->
        pure (ConstructedSnippet mempty (AfterAction [ \out -> action run st out ])
                                 pos pos (afterDraw action) (pure ()))
