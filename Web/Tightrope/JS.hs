{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Web.Tightrope.JS
    ( DOMImpl
    , Snippet, Attribute, Component
    , Node, RunAlgebra, EnterExit, EnterExitT
    , GenericRunAlgebra, EmbeddedAlgebraWrapper
    , RunAlgebraWrapper

    , TT.TightropeEventImpl(..)

    , jss
    , addStylesheet

    , mountComponent

    , customHandler

    , withDOMImpl
    , liftDom ) where

import           Prelude hiding (drop)

import           Web.Tightrope.Types hiding ( Node, RunAlgebra, EnterExit, EnterExitT
                                            , GenericRunAlgebra, EmbeddedAlgebraWrapper
                                            , RunAlgebraWrapper
                                            , liftDom )
import qualified Web.Tightrope.Types as TT
import qualified Web.Tightrope.Event as TT
import           Web.Tightrope.Attributes

import           Control.Concurrent.MVar hiding (modifyMVar, modifyMVar_)
import           Control.Monad.Catch (MonadMask, mask, onException, bracket)
import           Control.Monad
import           Control.Monad.Reader
import           Control.Monad.Writer (WriterT)
import           Control.Monad.State (StateT)

import           Data.Coerce
import           Data.IORef
import           Data.JSString (JSString)
import qualified Data.JSString as JSS
import qualified Data.JSString.Text as JSS
import           Data.Monoid
import           Data.Typeable

import qualified GHCJS.DOM as DOM
import qualified GHCJS.DOM.Element as DOM hiding (drop, error)
import qualified GHCJS.DOM.ElementCSSInlineStyle as DOM
import qualified GHCJS.DOM.Node as DOM
import qualified GHCJS.DOM.Text as DOM
import qualified GHCJS.DOM.Document as DOM hiding (drop, evaluate, error)
import qualified GHCJS.DOM.Types as DOM
import qualified GHCJS.DOM.EventTarget as DOM
import qualified GHCJS.DOM.HTMLInputElement as DOM
import qualified GHCJS.DOM.EventTargetClosures as DOM
import qualified GHCJS.DOM.EventM as DOM
import qualified GHCJS.DOM.Event as DOM
import qualified GHCJS.DOM.NodeList as DOM (getLength, item)
import qualified GHCJS.DOM.Window as DOM hiding (drop, getLength, error)
import qualified GHCJS.DOM.GlobalEventHandlers as DOM (resize)
import qualified GHCJS.DOM.RequestAnimationFrameCallback as DOM
import qualified GHCJS.DOM.DOMTokenList as TokenList
import           GHCJS.DOM.CSSStyleDeclaration as DOM hiding (getLength, item)
import qualified GHCJS.Types as DOM

import qualified Language.Javascript.JSaddle as JS

import           System.Mem.StableName
import           System.IO.Unsafe

#ifndef __GHCJS__
import qualified Data.HashMap.Strict as HM
import           Data.Int (Int64)
import           Data.Maybe (fromMaybe)
#endif

data DOMImpl

liftDom :: MonadDom DOMImpl m => JS.JSM a -> m a
liftDom = TT.liftDom (Proxy @DOMImpl)

instance RawIO DOM.JSM where
    rawIO = liftIO

instance MonadDom DOMImpl JS.JSM where
    liftDom _ = id

instance TightropeImpl DOMImpl where
    type Node DOMImpl = DOM.Node
    type Text DOMImpl = JSString
    data Event DOMImpl e where
      Event :: Coercible e DOM.Event => JSString -> Event DOMImpl e
    type DomM DOMImpl = DOM.JSM

#ifdef __GHCJS__
    getIORunner = pure (IORunner id)
#else
    getIORunner = JS.JSM $ do
                    ref <- ask
                    pure (IORunner (\f -> runReaderT (JS.unJSM f) ref))
#endif

    createElement _ tagName =
        do Just document <- DOM.currentDocument
           el <- DOM.createElement document tagName
           pure (DOM.toNode el)
    createTextNode _ txt =
        do Just document <- DOM.currentDocument
           t <- DOM.createTextNode document txt
           pure (DOM.toNode t)

    addEventListener n (Event evtName :: Event DOMImpl e) action =
        do let action' :: DOM.Event -> DOM.JSM ()
               action' e =
                 runReaderT action (coerce e)

           listener <- DOM.newListenerSync (ReaderT action')
           DOM.addListener (DOM.toEventTarget n) (DOM.unsafeEventName evtName) listener False

           pure $ do
             DOM.removeListener (DOM.toEventTarget n) (DOM.unsafeEventName evtName) listener False
             DOM.releaseListener listener

    addBodyEventListener e action =
        do Just document <- DOM.currentDocument
           Just body <- DOM.getBody document
           addEventListener (DOM.toNode body) e action

    addResizeListener _ action =
        do Just window <- DOM.currentWindow
           DOM.on window DOM.resize $ do
             dims <- (,) <$> (fromIntegral <$> DOM.getInnerWidth  window)
                         <*> (fromIntegral <$> DOM.getInnerHeight window)
             lift (action dims)

    insertAtPos _ (DOMInsertPos parent Nothing) child =
        do children <- DOM.getChildNodes parent
           childCount <- DOM.getLength children
           if childCount == 0
             then DOM.appendChild parent child
             else do
               firstChild <- DOM.item children 0
               DOM.insertBefore parent child firstChild
           pure (DOMInsertPos parent (Just child))
    insertAtPos _ (DOMInsertPos parent (Just prevSibling)) child =
        do nextSibling <- DOM.getNextSibling prevSibling
           case nextSibling of
             Nothing  -> DOM.appendChild parent child
             Just sib -> DOM.insertBefore parent child (Just sib)
           pure (DOMInsertPos parent (Just child))
    removeChild _ n =
        do parent <- DOM.getParentNode n
           case parent of
             Nothing -> pure ()
             Just parent -> do
               DOM.removeChild parent n
               pure ()

    addClasses p node classes =
        let classList = filter (not . JSS.null) (JSS.splitOn " " classes)
        in mapM_ (enableClass p node) classList
    enableClass _ node className =
        do classes <- DOM.getClassList (DOM.uncheckedCastTo DOM.Element node)
           TokenList.add classes [className]
    disableClass _ node className =
        do classes <- DOM.getClassList (DOM.uncheckedCastTo DOM.Element node)
           TokenList.remove classes [className]

    setAttribute _ n "class" Nothing = pure ()
    setAttribute _ n "class" (Just v) =
        DOM.setClassName (DOM.uncheckedCastTo DOM.Element n) v
    setAttribute _ n key Nothing = do
        DOM.removeAttribute (DOM.uncheckedCastTo DOM.Element n) key
        case key of
          "checked" ->  do
              n' <- DOM.castTo DOM.HTMLInputElement n
              case n' of
                Just n -> DOM.setChecked n False
                Nothing -> pure ()
          _ -> pure ()
    setAttribute _ n key (Just value) = do
        DOM.setAttribute (DOM.uncheckedCastTo DOM.Element n) key value
        case key of
          "checked" -> do
              n' <- DOM.castTo DOM.HTMLInputElement n
              case n' of
                Just n -> DOM.setChecked n $
                          case value of
                            "checked" -> True
                            _ -> False
                Nothing -> pure ()
          _ -> pure ()

    setStyle _ n key Nothing =
        do style <- DOM.getStyle (DOM.uncheckedCastTo DOM.ElementCSSInlineStyle n)
           DOM.removeProperty style key :: DOM.JSM JSString
           pure ()
    setStyle _ n key (Just value) =
        do style <- DOM.getStyle (DOM.uncheckedCastTo DOM.ElementCSSInlineStyle n)
           DOM.setProperty style key value (Just (JSS.pack ""))
           pure ()

    setNodeValue _ n value =
        DOM.setNodeValue n (Just value)

    requestFrame _ = requestAnimationFrameHs

instance AttrValue JSString where
    type AttrValueState JSString = JSString

    attrValue _ _ x = (x, Just . JS.fromJSString $ x)

-- * Specializations

type Snippet = Snippet' DOMImpl
type Attribute = Attribute' DOMImpl
type Component = Component' DOMImpl
type Node = TT.Node DOMImpl
type RunAlgebra x = TT.RunAlgebra DOMImpl x
type RunAlgebraWrapper x = TT.RunAlgebraWrapper DOMImpl x
type GenericRunAlgebra x = TT.GenericRunAlgebra DOMImpl x
type EmbeddedAlgebraWrapper = TT.EmbeddedAlgebraWrapper DOMImpl
type EnterExit = TT.EnterExit DOMImpl
type EnterExitT = TT.EnterExitT DOMImpl

-- * Browser DOM-specific utility functions

jss :: JSString -> JSString
jss = id

addStylesheet :: JSString -> DOM.JSM ()
addStylesheet loc =
    do Just document <- DOM.currentDocument
       Just head <- DOM.getHead document

       link <- DOM.createElement document ("link" :: JSString)
       DOM.setAttribute link ("rel" :: JSString) ("stylesheet" :: JSString)
       DOM.setAttribute link ("type" :: JSString) ("text/css" :: JSString)
       DOM.setAttribute link ("href" :: JSString) loc

       DOM.appendChild head link
       pure ()

-- * Top-level component attachment

#ifdef __GHCJS__
{-# NOINLINE _animFrameCallbackVar #-}
_animFrameCallbackVar :: MVar (Maybe DOM.RequestAnimationFrameCallback, Maybe Int, [ Double -> DOM.JSM () ])
_animFrameCallbackVar =
    unsafePerformIO (newMVar (Nothing, Nothing, mempty))
#else
{-# NOINLINE _animFrameCallbackVar #-}
_animFrameCallbackVar :: MVar (HM.HashMap Int64 (Maybe DOM.RequestAnimationFrameCallback, Maybe Int, [ Double -> DOM.JSM () ]))
_animFrameCallbackVar =
    unsafePerformIO (newMVar mempty)
#endif

modifyMVar :: (MonadMask m, MonadIO m) => MVar a -> (a -> m (a, b)) -> m b
modifyMVar var x = mask $ \unmask -> do
                     val <- liftIO (takeMVar var)
                     (val', ret) <- x val `onException` liftIO (putMVar var val)
                     liftIO (putMVar var val')
                     pure ret


modifyMVar_ :: (MonadMask m, MonadIO m) => MVar a -> (a -> m a) -> m ()
modifyMVar_ var x = modifyMVar var (\a -> do
                                      a' <- x a
                                      pure (a', ()))

#ifdef __GHCJS__
modifyInContext = id
#else
modifyInContext go v = do
  ctx <- JS.askJSM
  let vars = HM.lookup (JS.contextId ctx) v
  (new, ret) <- go (fromMaybe (Nothing, Nothing, mempty) vars)
  let v' = HM.insert (JS.contextId ctx) new v
  v' `seq` pure (v', ret)
#endif

requestAnimationFrameHs :: (Double -> DOM.JSM ()) -> DOM.JSM ()
requestAnimationFrameHs doDraw = do
  modifyMVar _animFrameCallbackVar . modifyInContext $ \(cb, existing, reqs) ->
    do let reqs' = doDraw:reqs

       cb' <-
           case cb of
             Just cb -> pure cb
             Nothing -> DOM.newRequestAnimationFrameCallbackAsync _doRedraw
       existing' <-
           case existing of
             Just _ -> pure existing
             Nothing -> do
               Just window <- DOM.currentWindow
               Just <$> DOM.requestAnimationFrame window cb'
       pure (reqs' `seq` (Just cb', existing', reqs'), ())

  where
    _doRedraw ts =
        do reqs <- modifyMVar _animFrameCallbackVar . modifyInContext $ \(cb, existing, reqs) ->
                   if null reqs
                      then pure ((cb, Nothing, mempty), mempty)
                      else pure ((cb, existing, mempty), reqs)
           if null reqs then pure ()
              else do
                forM_ reqs $ \req ->
                  req ts
                _doRedraw ts

mountComponent :: DOM.Element -> props -> Component props algebra DOM.JSM -> DOM.JSM (props -> DOM.JSM ())
mountComponent el initialProps (Component mkSt emptyOut runAlgebra onCreate onPropsChange (Snippet create :: Snippet out st algebra))  =
  do stVar <- liftIO $ newEmptyMVar
     intStVar <- liftIO $ newIORef (error "intStVar not set")
     outVar <- liftIO $ newIORef (error "outVar not set")
     syncVar <- liftIO $ newMVar ()

     Just window <- DOM.currentWindow

     isDirtyV <- liftIO $ newIORef False
     let redraw _ = do liftIO (atomicWriteIORef isDirtyV False)
                       (st, (Snippet update, _)) <-
                           bracket (liftIO $ takeMVar stVar) (liftIO . putMVar stVar) $ \st ->
                           (st,) <$> liftIO (readIORef intStVar)


                       ConstructedSnippet (Endo mkOut) scheduled _ _ update' finish <-
                           update runAlgebra' st (liftIO $ readMVar stVar) (DOMInsertPos (DOM.toNode el) Nothing)

                       liftIO (atomicWriteIORef intStVar (update', finish))

                       let out' = mkOut emptyOut
                       liftIO $ atomicWriteIORef outVar out'

                       runAfterAction scheduled out'

         runAlgebra' :: forall a. algebra a -> DOM.JSM a
         runAlgebra' a =

             do (x, shouldRedraw) <- modifyMVar stVar $ \st ->
                     do out <- liftIO $ readIORef outVar
--                        (update', finish) <- readIORef intStVar
                        oldStNm <- liftIO $ makeStableName st
                        (x, !st') <- runAlgebra (TT.EnterExit (liftIO . putMVar stVar) (liftIO $ takeMVar stVar) id runAlgebra') st out a
                        newStNm <- liftIO $ makeStableName st'
                        pure (st', (x, oldStNm /= newStNm))

                when shouldRedraw scheduleRedraw

                pure x
         scheduleRedraw = do
           wasDirty <- liftIO (atomicModifyIORef isDirtyV (\isDirty -> (True, isDirty)))
           when (not wasDirty) (requestAnimationFrameHs redraw)

         getSt = liftIO (readMVar stVar)
         initialState = mkSt initialProps

     liftIO $ putMVar stVar initialState
     ConstructedSnippet (Endo mkOut) scheduled _ _ update finish <-
         create runAlgebra' initialState getSt (DOMInsertPos (DOM.toNode el) Nothing)

     liftIO $ atomicWriteIORef intStVar (update, finish)

     let !initialOut = mkOut emptyOut
     liftIO $ atomicWriteIORef outVar initialOut

     runAfterAction scheduled initialOut
     runAlgebra' (onCreate runAlgebra' initialProps)

     pure (\newProps -> runAlgebra' (onPropsChange newProps))

-- * Events

instance TT.TightropeEventImpl DOMImpl where
    type MouseEventImpl DOMImpl = DOM.MouseEvent
    type KeyboardEventImpl DOMImpl = DOM.KeyboardEvent
    type ClipboardEventImpl DOMImpl = DOM.ClipboardEvent
    type EventImpl DOMImpl = DOM.Event

    dblClick = Event "dblclick"
    click = Event "click"

    keyDown = Event "keydown"
    keyUp = Event "keyup"
    keyPress = Event "keypress"

    mouseUp = Event "mouseup"
    mouseDown = Event "mousedown"
    mouseEnter = Event "mouseenter"
    mouseLeave = Event "mouseleave"
    mouseOver = Event "mouseover"
    mouseOut = Event "mouseout"
    mouseMove = Event "mousemove"
    contextMenu = Event "contextmenu"

    drag = Event "drag"
    drop = Event "drop"
    dragStart = Event "dragstart"
    dragEnd = Event "dragend"
    dragEnter = Event "dragenter"
    dragLeave = Event "dragleave"
    dragOver = Event "dragover"

    cutEvent = Event "cut"
    copyEvent = Event "copy"
    pasteEvent = Event "paste"

    focusEvent = Event "focus"
    blurEvent = Event "blur"
    change = Event "change"

-- * Custom events

customHandler ::
     forall evt out state algebra.
     (Node -> JS.JSVal -> DOM.JSM ())
  -> (Node -> JS.JSVal -> DOM.JSM ())
  -> (RunAlgebra algebra -> state -> DOM.JSVal -> DOM.JSM ())
  -> Attribute out state algebra
customHandler attachHandler detachHandler handler =
    Attribute $
    Snippet (\run st getSt pos@(DOMInsertPos n _) -> do
               let handler' e = getSt >>= \st -> handler run st e

               listener <- JS.toJSVal (JS.fun $ \_ _ [e] -> handler' e)
               attachHandler n listener

               let finish = detachHandler n listener
               pure (ConstructedSnippet mempty mempty pos pos (go finish) finish))

  where
    go finish = Snippet $ \_ _ _ pos ->
                pure (ConstructedSnippet mempty mempty pos pos (go finish) finish)

withDOMImpl :: TightropeImpl impl => Proxy impl -> a -> ((impl :~: DOMImpl) -> a) -> a
withDOMImpl Proxy otherwise action =
    maybe otherwise action eqT
