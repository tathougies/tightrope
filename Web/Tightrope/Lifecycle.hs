module Web.Tightrope.Lifecycle where

import Web.Tightrope.Types

onCreate :: forall impl state algebra out.
            (state -> algebra ()) -> Snippet' impl out state algebra
onCreate action = Snippet $ \run st _ pos ->
                  pure (ConstructedSnippet mempty (AfterAction [ const (run (action st)) ])
                                           pos pos emptySnippet (pure ()))

onFinish :: (state -> IO ()) -> Snippet' impl out state algebra
onFinish action = Snippet $ \run st _ pos ->
                  pure (ConstructedSnippet mempty mempty pos pos (onFinish action) (action st))

afterDraw :: forall impl state out algebra.
             (RunAlgebra algebra -> state -> out -> IO ())
          -> Snippet' impl out state algebra
afterDraw action =
    Snippet $ \run st _ pos ->
        pure (ConstructedSnippet mempty (AfterAction [ \out -> action run st out ])
                                 pos pos (afterDraw action) (pure ()))
