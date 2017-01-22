module Web.Tightrope.Lifecycle where

import Web.Tightrope.Types

onCreate :: forall impl state algebra out parentAlgebra.
            (state -> algebra ()) -> Snippet' impl () out state algebra parentAlgebra
onCreate action = Snippet create' update' (\_ -> pure ())
    where create' run st _ pos =
              pure (ConstructedSnippet mempty (AfterAction [ const (run (action st)) ])
                                       pos pos ())
          update' _ _ _ pos () =
              pure (ConstructedSnippet mempty mempty pos pos ())

afterDraw :: forall impl state out algebra parentAlgebra.
             (RunAlgebra algebra -> state -> out -> IO ())
          -> Snippet' impl () out state algebra parentAlgebra
afterDraw action =
    Snippet create' update' (\_ -> pure ())
  where
    create' :: RunAlgebra algebra -> state -> IO state -> SnippetConstructor impl () out
    create' run st _ pos =
        pure (ConstructedSnippet mempty (AfterAction [ \out -> action run st out ])
                                 pos pos ())
    update' :: RunAlgebra algebra -> state -> IO state -> SnippetUpdater impl () out
    update' run st _ pos () =
        pure (ConstructedSnippet mempty (AfterAction [ \out -> action run st out ])
                                 pos pos ())

