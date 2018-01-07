module Web.Tightrope.Event
    ( on, onBodyEvent, onWindowResize

    , TightropeEventImpl(..) ) where

import Web.Tightrope.Types

import Control.Monad.Reader
import Control.Monad.IO.Class

import Data.Proxy

import GHC.TypeLits

finishEventHandler :: IO () -> Snippet' impl out st algebra
finishEventHandler finish =
    Snippet $ \_ _ _ pos ->
    pure (ConstructedSnippet mempty mempty pos pos (finishEventHandler finish) finish)

on, onBodyEvent ::
    forall impl evt evtName algebra out state.
    TightropeImpl impl => Event impl evt
 -> (GenericRunAlgebra algebra -> state -> ReaderT evt IO ())
 -> Attribute' impl out state algebra
on evt action =
    Attribute $
    Snippet (\run st getSt pos@(DOMInsertPos n _) -> do
             let runAlgebra' :: forall a m. MonadIO m => algebra a -> m a
                 runAlgebra' x = liftIO (run x)

             finish <- addEventListener n evt (liftIO getSt >>= action runAlgebra')
             pure (ConstructedSnippet mempty mempty pos pos
                                      (finishEventHandler finish) finish))

onBodyEvent evt action =
    Attribute $
    Snippet (\run st getSt pos@(DOMInsertPos n _) -> do
               let runAlgebra' :: forall a m. MonadIO m => algebra a -> m a
                   runAlgebra' x = liftIO (run x)

               finish <- addBodyEventListener evt (liftIO getSt >>= action runAlgebra')

               pure (ConstructedSnippet mempty mempty pos pos (finishEventHandler finish) finish))

onWindowResize ::
    forall impl algebra out state. TightropeImpl impl =>
    (GenericRunAlgebra algebra -> state -> (Double, Double) -> IO ())
 -> Attribute' impl out state algebra
onWindowResize action =
    Attribute $
    Snippet (\run st getSt pos -> do
               let runAlgebra' :: forall a m. MonadIO m => algebra a -> m a
                   runAlgebra' x = liftIO (run x)

               finish <- addResizeListener (Proxy :: Proxy impl) $
                         \dims -> do
                           st <- getSt
                           action runAlgebra' st dims

               pure (ConstructedSnippet mempty mempty pos pos (finishEventHandler finish) finish))

class TightropeImpl impl => TightropeEventImpl impl where
    type MouseEventImpl impl :: *
    type KeyboardEventImpl impl :: *
    type ClipboardEventImpl impl :: *
    type EventImpl impl :: *

    click, dblClick, mouseUp, mouseDown, mouseEnter, mouseLeave, mouseOver,
      mouseOut, mouseMove, contextMenu :: Event impl (MouseEventImpl impl)
    keyDown, keyUp, keyPress :: Event impl (KeyboardEventImpl impl)
    drag, drop, dragStart, dragEnd, dragEnter, dragLeave, dragOver :: Event impl (MouseEventImpl impl)
    cutEvent, copyEvent, pasteEvent :: Event impl (ClipboardEventImpl impl)
    change, focusEvent, blurEvent :: Event impl (EventImpl impl)

instance TightropeEventImpl DummyImpl where
    type MouseEventImpl DummyImpl = ()
    type KeyboardEventImpl DummyImpl = ()
    type ClipboardEventImpl DummyImpl = ()
    type EventImpl DummyImpl = ()

    dblClick    = DummyEvent
    click       = DummyEvent

    keyDown     = DummyEvent
    keyUp       = DummyEvent
    keyPress    = DummyEvent

    mouseUp     = DummyEvent
    mouseDown   = DummyEvent
    mouseEnter  = DummyEvent
    mouseLeave  = DummyEvent
    mouseOver   = DummyEvent
    mouseOut    = DummyEvent
    mouseMove   = DummyEvent
    contextMenu = DummyEvent

    drag        = DummyEvent
    drop        = DummyEvent
    dragStart   = DummyEvent
    dragEnd     = DummyEvent
    dragEnter   = DummyEvent
    dragLeave   = DummyEvent
    dragOver    = DummyEvent

    cutEvent    = DummyEvent
    copyEvent   = DummyEvent
    pasteEvent  = DummyEvent

    focusEvent  = DummyEvent
    blurEvent   = DummyEvent
    change      = DummyEvent

