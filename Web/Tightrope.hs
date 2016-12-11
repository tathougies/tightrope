{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE JavaScriptFFI #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeOperators #-}

module Web.Tightrope where

import Control.Concurrent.MVar
import Control.Concurrent
import Control.Exception (bracket, evaluate)

import Control.Monad.State
import Control.Monad.Reader
--import Control.Monad.Writer
import Control.Monad hiding (forM_, forM)

import Data.IORef
import Data.Monoid
import Data.Maybe
import Data.JSString (JSString)
import Data.Traversable (forM)
import Data.Foldable (forM_, toList)
import qualified Data.JSString as JSS
import qualified Data.Text as T
import Data.JSString.Text
import Data.String (fromString)

import GHCJS.DOM
import GHCJS.DOM.Element hiding (drop, error)
import GHCJS.DOM.Node
import GHCJS.DOM.Text
import GHCJS.DOM.Document hiding (drop, evaluate, error)
import GHCJS.DOM.Types
import GHCJS.DOM.EventTarget
import GHCJS.DOM.HTMLInputElement
import GHCJS.DOM.EventTargetClosures
import GHCJS.DOM.EventM
import GHCJS.DOM.Event
import GHCJS.DOM.NodeList (getLength, item)
import GHCJS.DOM.Window hiding (drop, getLength, error)
import GHCJS.DOM.RequestAnimationFrameCallback
import qualified GHCJS.DOM.DOMTokenList as TokenList
import GHCJS.DOM.CSSStyleDeclaration hiding (getLength, item)
import GHCJS.Foreign.Callback
import GHCJS.Types

import System.Mem.StableName
import System.IO.Unsafe

type RunAlgebra algebra = forall a. algebra a -> IO a
type GenericRunAlgebra algebra = forall a m. MonadIO m => algebra a -> m a
type StatefulAlgebra state out parentAlgebra = EnterExitT state out parentAlgebra

data EnterExit state m = EnterExit (state -> m ()) (m state)

newtype RunAlgebraWrapper algebra = RunAlgebraWrapper (RunAlgebra algebra)
newtype EmbeddedAlgebraWrapper algebra parentAlgebra = EmbeddedAlgebraWrapper (forall a. algebra a -> parentAlgebra a)
newtype EnterExitT state out m a = EnterExitT { runEnterExitT :: EnterExit state m -> out -> state -> m (a, state) }

data DOMInsertPos
    = DOMInsertPos
    { insertPosParent :: Node
    , insertPosPrevSibling :: Maybe Node }

newtype AfterAction out = AfterAction [ out -> IO () ]

type SnippetConstructor intSt out = DOMInsertPos -> IO (ConstructedSnippet intSt out)
type SnippetUpdater intSt out = DOMInsertPos -> intSt -> IO (ConstructedSnippet intSt out)
data ConstructedSnippet intSt out
    = ConstructedSnippet
    { constructedSnippetOut  :: Endo out
    , constructedAfterAction :: AfterAction out
    , constructedSiblingPos  :: DOMInsertPos
    , constructedChildPos    :: DOMInsertPos
    , constructedState       :: intSt }

-- type SnippetConstructor internalSt out = StateT DOMInsertPos (WriterT (Endo out, AfterAction out) IO) (DOMInsertPos, internalSt)
-- type SnippetUpdater internalSt out = StateT (DOMInsertPos, internalSt) (WriterT (Endo out, AfterAction out) IO) DOMInsertPos

data a :++ b = !a :++ !b

data Snippet internalSt out state algebra (parentAlgebra :: * -> *)
    = Snippet
    { snippetCreateUnder :: RunAlgebra algebra -> state -> SnippetConstructor internalSt out
    , snippetUpdateElem  :: state -> SnippetUpdater internalSt out
    , snippetFinish      :: ReaderT internalSt IO () }

data Attribute attrSt state algebra (parentAlgebra :: * -> *)
    = Attribute
    { attributeSet    :: RunAlgebra algebra -> state -> Node -> IO attrSt
    , attributeUpdate :: state -> Node -> attrSt -> IO attrSt
    , attributeFinish :: ReaderT attrSt IO () }

data Component (algebra :: * -> *) (parentAlgebra :: * -> *) where
    Component :: MonadIO parentAlgebra =>
                 { componentStateInitial :: state
                 , componentEmptyOut     :: out
                 , componentRunAlgebra   :: forall a. EnterExit state parentAlgebra -> state -> out -> algebra a -> parentAlgebra (a, state)
                 , componentOnConstruct  :: RunAlgebra algebra -> algebra ()
                 , componentTemplate     :: Snippet internalSt out state algebra parentAlgebra }
              -> Component algebra parentAlgebra

data MountedComponent algebra parentAlgebra where
    MountedComponent :: MonadIO parentAlgebra =>
                        { mountedStateV   :: MVar state
                        , mountedIntStateV :: IORef internalSt
                        , mountedOutV     :: IORef out
                        , mountedInsPosV  :: MVar (DOMInsertPos, DOMInsertPos, DOMInsertPos)
                        , mountedEmptyOut :: out
                        , mountedAlgebraWrapper :: EmbeddedAlgebraWrapper algebra parentAlgebra
                        , mountedFinish   :: IO ()
                        , mountedRunAlgebra :: forall a. EnterExit state parentAlgebra -> state -> out -> algebra a ->  parentAlgebra (a, state)
                        , mountedTemplate :: Snippet internalSt out state algebra parentAlgebra }
                     -> MountedComponent algebra parentAlgebra

data SomeSnippet out st algebra parentAlgebra where
    SomeSnippet ::
        Snippet internalSt out st algebra parentAlgebra ->
        SomeSnippet out st algebra parentAlgebra

data RenderedSnippet out st where
    RenderedSnippet ::
        !intSt ->
        (st -> SnippetUpdater intSt out) ->
        ReaderT intSt IO () ->
        RenderedSnippet out st

data Embedded index parent current
    = Embedded { parent :: parent
               , current :: current
               , index :: index }

instance Monoid (AfterAction out) where
    mempty = AfterAction []
    mappend (AfterAction a) (AfterAction b) = AfterAction (a <> b)

runAfterAction :: AfterAction out -> out -> IO ()
runAfterAction act out = go' act out
    where go' (AfterAction []) out = pure ()
          go' (AfterAction (x:xs)) out = x out >> go' (AfterAction xs) out

class RawIO m where
    rawIO :: IO a -> m a

foreign import javascript unsafe "console.log($1, $2, $3);" js_log :: Node -> Node -> Node -> IO ()
foreign import javascript unsafe "console.log($1, $2);" js_log2 :: Node -> Node -> IO ()
foreign import javascript unsafe "console.log($1);" js_log1 :: Node -> IO ()
foreign import javascript unsafe "console.log($1);" js_logEvent :: Event -> IO ()
loginsertpos (DOMInsertPos parent Nothing) = js_log1 parent
loginsertpos (DOMInsertPos parent (Just node)) = js_log2 parent node

{-# NOINLINE _animFrameCallbackVar #-}
_animFrameCallbackVar :: MVar (Maybe RequestAnimationFrameCallback, Maybe Int, [ Double -> IO () ])
_animFrameCallbackVar =
    unsafePerformIO (newMVar (Nothing, Nothing, mempty))

requestAnimationFrameHs :: (Double -> IO ()) -> IO ()
requestAnimationFrameHs doDraw = do
  putStrLn "request animation frame"
  modifyMVar_ _animFrameCallbackVar $ \(cb, existing, reqs) ->
    do let reqs' = doDraw:reqs

       cb' <-
           case cb of
             Just _ -> pure cb
             Nothing -> Just <$> newRequestAnimationFrameCallback _doRedraw
       existing' <-
           case existing of
             Just _ -> pure existing
             Nothing -> do
               Just window <- currentWindow
--               putStrLn "REquest animation frame js"
               Just <$> requestAnimationFrame window cb'
       pure (reqs' `seq` (cb', existing', reqs'))
--  putStrLn "Done reuest frame"

  where
    _doRedraw ts =
        do -- putStrLn "_doRedraw"
           reqs <- modifyMVar _animFrameCallbackVar $ \(cb, existing, reqs) ->
                   if null reqs
                      then pure ((cb, Nothing, mempty), mempty)
                      else pure ((cb, existing, mempty), reqs)
           putStrLn ("Have " <> show (length reqs) <> " to go")
           if null reqs then putStrLn "Done drawing" >> pure ()
              else do
                forM_ reqs $ \req ->
                  req ts
                _doRedraw ts

insertAtPos :: DOMInsertPos -> Node -> IO DOMInsertPos
insertAtPos (DOMInsertPos parent Nothing) child =
    do children <- getChildNodes parent
       childCount <- maybe (pure 0) getLength children
       case (children, childCount) of
         (_, 0) -> appendChild parent (Just child)
         (Nothing, _) -> appendChild parent (Just child)
         (Just children, _) ->
             do Just firstChild <- item children 0
                insertBefore parent (Just child) (Just firstChild)
       pure (DOMInsertPos parent (Just child))
insertAtPos (DOMInsertPos parent (Just prevSibling)) child =
    do nextSibling <- getNextSibling prevSibling
       case nextSibling of
         Nothing  -> appendChild parent (Just child)
         Just sib -> insertBefore parent (Just child) (Just sib)
       pure (DOMInsertPos parent (Just child))

dynClass :: forall st algebra parentAlgebra.
            JSString -> (st -> Bool) -> Attribute Bool st algebra parentAlgebra
dynClass className dyn = Attribute set update finish
    where set :: RunAlgebra algebra -> st -> Node -> IO Bool
          set update st node =
              do let enabled = dyn st
                 if enabled
                   then liftIO (enableClass node)
                   else liftIO (disableClass node)
                 pure enabled

          update st node enabled =
              do let enabled' = dyn st

                 when (enabled' /= enabled) $
                      if enabled'
                      then liftIO (enableClass node)
                      else liftIO (disableClass node)

                 pure enabled'

          finish = pure ()

          enableClass node =
              do el <- castToElement node
                 classes <- getClassList el
                 case classes of
                   Just classes ->
                       TokenList.add classes [className]
                   _ -> pure ()
          disableClass node =
              do el <- castToElement node
                 classes <- getClassList el
                 case classes of
                   Just classes ->
                       TokenList.remove classes [className]
                   _ -> pure ()

-- splitOn :: Char -> String -> [String]
-- splitOn _ "" = []
-- splitOn needle haystack =
--     let (x, xs) = break (== needle) haystack
--     in case x of
--          "" | x:_ <- xs, x == needle -> splitOn needle xs
--          _ -> case xs of
--                 "" -> [x]
--                 _:xs -> x:splitOn needle xs

class Attrable a st where
    type AttrIntState a st :: *

    attr :: JSString -> a -> Attribute (AttrIntState a st) st algebra parentAlgebra

instance Attrable JSString st where
    type AttrIntState JSString st = ()

    attr name val = Attribute set update finish
        where set _ _ n = do n <- castToElement n
                             setAttribute n name val
                             pure ()
              update _ _ =  pure
              finish = pure ()

instance Attrable T.Text st where
    type AttrIntState T.Text st = ()

    attr name val = Attribute set update finish
        where set _ _ n = do n <- castToElement n
                             setAttribute n name val
                             pure ()
              update _ _ =  pure
              finish = pure ()

instance Attrable Bool st where
    type AttrIntState Bool st = AttrIntState JSString st

    attr name True = attr name name
    attr name False = Attribute (\_ _ _ -> pure ()) (\_ _ -> pure) (pure ())

instance (st ~ st', x ~ x', Eq x) => Attrable (x -> Maybe JSString, st -> x') st' where
    type AttrIntState (x -> Maybe JSString, st -> x') st' = x

    attr name (mkString, mkValue) = Attribute set update finish
      where set _ st n =
                do let curString = mkString curValue
                       curValue = mkValue st
                   case curString of
                     Just curString ->
                         doSet n name curString
                     Nothing -> pure ()
                   pure curValue
            update st n curValue =
                do let newString = mkString newValue
                       newValue = mkValue st
                   when (curValue /= newValue) $
                        case newString of
                          Just newString ->
                              doSet n name newString
                          Nothing ->
                              doRemove n name
                   pure newValue
            finish = pure ()

            doRemove n name = do n <- liftIO (castToElement n)
                                 removeAttribute n name
                                 case name of
                                   "checked" ->
                                       do n <- liftIO (castToHTMLInputElement n)
                                          setChecked n False
                                   _ -> pure ()

            doSet n name value = do n <- liftIO (castToElement n)
                                    setAttribute n name value
                                    case name of
                                      "checked" ->
                                          do n <- liftIO (castToHTMLInputElement n)
                                             setChecked n (value == "checked")
                                      _ -> pure ()

instance (st ~ st', AttrValue x) => Attrable (st -> x) st' where
    type AttrIntState (st -> x) st' = Maybe JSString

    attr name mkValue = attr name (id :: Maybe JSString -> Maybe JSString, attrValue name . mkValue :: st -> Maybe JSString)

class Stylable x st where
    type StylableIntState x st :: *

    style_ :: JSString -> x -> Attribute (StylableIntState x st) st algebra parentAlgebra

instance Stylable JSString st where
    type StylableIntState JSString st = ()

    style_ name val = Attribute set (\_ _ -> pure) (pure ())
        where set _ _ n = do n <- castToElement n
                             Just style <- getStyle n
                             setProperty style name (Just val) ("" :: JSString)
                             pure ()

instance (st ~ st', AttrValue x) => Stylable (st -> x) st' where
    type StylableIntState (st -> x) st' = x

    style_ name mkValue = style_ name ( attrValue name :: x -> Maybe JSString
                                      , mkValue :: st -> x )

instance (st ~ st', x ~ x', Eq x) => Stylable ( x -> Maybe JSString, st -> x' ) st' where
    type StylableIntState ( x -> Maybe JSString, st -> x' ) st' = x

    style_ name ( mkString, mkValue) = Attribute set update finish
        where set _ st n =
                  do let curValueJS = mkString curValue
                         curValue = mkValue st
                     case curValueJS of
                       Just curValueJS ->
                           do Just style <-
                                  do n <- castToElement n
                                     getStyle n
                              setProperty style name (Just curValueJS) ("" :: JSString)
                       Nothing -> pure ()
                     pure curValue

              update st n curValue =
                  do let newValueJS = mkString newValue
                         newValue = mkValue st
                     n <- castToElement n
                     Just style <- getStyle n
                     when (curValue /= newValue) $
                          case newValueJS of
                            Just newValueJS ->
                                setProperty style name (Just newValueJS) ("" :: JSString)
                            Nothing ->
                                void (removeProperty style name :: IO (Maybe JSString))
                     pure newValue
              finish = pure ()

class Ord x => AttrValue x where
    attrValue :: JSString -> x -> Maybe JSString
instance (AttrValue x, Ord x) => AttrValue (Maybe x) where
    attrValue _ Nothing = Nothing
    attrValue nm (Just x) = attrValue nm x
instance AttrValue JSString where
    attrValue _ = Just
instance AttrValue T.Text where
    attrValue _ = Just . textToJSString
instance AttrValue String where
    attrValue _ = Just . fromString
instance AttrValue Bool where
    attrValue _ False = Nothing
    attrValue name True = Just name

class FromEvent evt where
    fromEvent :: Event -> IO evt

instance FromEvent Event where
    fromEvent = pure
instance FromEvent MouseEvent where
    fromEvent = castToMouseEvent
instance FromEvent KeyboardEvent where
    fromEvent = castToKeyboardEvent
instance FromEvent UIEvent where
    fromEvent = castToUIEvent
instance FromEvent FocusEvent where
    fromEvent = castToFocusEvent

jss :: JSString -> JSString
jss = id

onBodyEvent ::
    forall evt algebra state parentAlgebra.
    FromEvent evt => EventName Element evt ->
    ((forall a. algebra a -> EventM Element evt a) -> state -> EventM Element evt ()) ->
    Attribute (IO (), IORef state) state algebra parentAlgebra
onBodyEvent (EventName evtName) handler =
    Attribute set update finish
  where
    set :: RunAlgebra algebra -> state -> Node -> IO (IO (), IORef state)
    set runAlgebra st n =
        do stRef <- liftIO (newIORef st)
           listener <- eventListenerNew (handler' stRef runAlgebra)

           Just document <- currentDocument
           Just body <- getBody document
           addEventListener document evtName (Just listener) False

           let finish = do removeEventListener document evtName (Just listener) False
                           eventListenerRelease listener

           pure (finish, stRef)

    handler' :: IORef state -> RunAlgebra algebra -> Event -> IO ()
    handler' stRef runAlgebra evt =
        do st <- readIORef stRef
           let runAlgebra' :: forall a. algebra a -> EventM Element evt a
               runAlgebra' x = lift (runAlgebra x)
           runReaderT (handler runAlgebra' st) =<< fromEvent evt

    update st _ intSt@(_, stRef) =
        do writeIORef stRef st
           pure intSt

    finish = do (release, _) <- ask
                liftIO release

onWindowEvent ::
    forall evt algebra state parentAlgebra.
    FromEvent evt => EventName Window evt ->
        ((forall a. algebra a -> EventM Window evt a) -> state -> EventM Window evt ()) ->
        Attribute (IO (), IORef state) state algebra parentAlgebra
onWindowEvent (EventName evtName) handler =
    Attribute set update finish
    where
      set :: RunAlgebra algebra -> state -> Node -> IO (IO (), IORef state)
      set runAlgebra st n =
          do stRef <- liftIO (newIORef st)
             listener <- eventListenerNew (handler' stRef runAlgebra)

             Just window <- currentWindow
             addEventListener window evtName (Just listener) False

             let finish = do removeEventListener window evtName (Just listener) False
                             eventListenerRelease listener

             pure (finish, stRef)

      handler' :: IORef state -> RunAlgebra algebra -> Event -> IO ()
      handler' stRef runAlgebra evt =
          do st <- readIORef stRef
             let runAlgebra' :: forall a. algebra a -> EventM Window evt a
                 runAlgebra' x = lift (runAlgebra x)
             runReaderT (handler runAlgebra' st) =<< fromEvent evt

      update st _ intSt@(_, stRef) =
          do writeIORef stRef st
             pure intSt

      finish = do (release, _) <- ask
                  liftIO release

onWindowResize :: forall algebra state parentAlgebra.
                  ((forall a. algebra a -> EventM Window Event a) -> state -> EventM Window Event ()) ->
                  Attribute (IO (), IORef state) state algebra parentAlgebra
onWindowResize = onWindowEvent (EventName "resize")

withUpdater :: forall out state algebra parentAlgebra.
               (RunAlgebraWrapper algebra -> out -> out)
            -> Snippet (RunAlgebraWrapper algebra) out state algebra parentAlgebra
withUpdater set = Snippet set' update (pure ())
    where set' :: RunAlgebra algebra -> state -> SnippetConstructor (RunAlgebraWrapper algebra) out
          set' update _ pos =
              pure (ConstructedSnippet (Endo (set (RunAlgebraWrapper update)))
                                       mempty
                                       pos pos
                                       (RunAlgebraWrapper update))

          update _ pos updater =
              pure (ConstructedSnippet (Endo (set updater)) mempty
                                       pos pos updater)

onCreate :: forall state algebra out parentAlgebra.
            (state -> algebra ()) -> Snippet () out state algebra parentAlgebra
onCreate action = Snippet create' update' (pure ())
    where create' run st pos =
              pure (ConstructedSnippet mempty (AfterAction [ const (run (action st)) ])
                                       pos pos ())
          update' _ pos () =
              pure (ConstructedSnippet mempty mempty pos pos ())

afterDraw :: forall state out algebra parentAlgebra.
             (RunAlgebra algebra -> state -> out -> IO ())
          -> Snippet (RunAlgebraWrapper algebra) out state algebra parentAlgebra
afterDraw action =
    Snippet create' update' (pure ())
  where
    create' :: RunAlgebra algebra -> state -> SnippetConstructor (RunAlgebraWrapper algebra) out
    create' run st pos =
        pure (ConstructedSnippet mempty (AfterAction [ \out -> action run st out ])
                                 pos pos (RunAlgebraWrapper run))
    update' st pos run'@(RunAlgebraWrapper run) =
        pure (ConstructedSnippet mempty (AfterAction [ \out -> action run st out ])
                                 pos pos run')

-- onChanges :: forall state key algebra parentAlgebra.
--              Eq key => (state -> key) -> (state -> algebra ())
--           -> Attribute (key, RunAlgebraWrapper algebra) state algebra parentAlgebra
-- onChanges mkKey action =
--     Attribute set' update' (pure ())
--     where set' :: RunAlgebra algebra -> state -> Node -> IO ((key, RunAlgebraWrapper algebra), AfterAction)
--           set' run st _ =
--               pure ((mkKey st, RunAlgebraWrapper run), AfterAction (run (action st)))
--           update' st _ =
--               do (pos, (oldKey, RunAlgebraWrapper run)) <- get

--                  let newKey = mkKey st
--                  if newKey /= oldKey
--                     then do
--                       put (pos, (newKey, RunAlgebraWrapper run))
--                       pure (AfterAction (run (action st)))
--                     else pure mempty

customHandler ::
    forall evt algebra state parentAlgebra.
    (Node -> Callback (JSVal -> IO ()) -> IO ()) -> (Node -> Callback (JSVal -> IO ()) -> IO ())
 -> (RunAlgebra algebra -> state -> JSVal -> IO ())
 -> Attribute (IO (), IORef state) state algebra parentAlgebra
customHandler attachHandler detachHandler handler =
    Attribute set update finish
  where
    set :: RunAlgebra algebra -> state -> Node -> IO (IO (), IORef state)
    set runAlgebra st n =
        do stRef <- liftIO (newIORef st)

           let handler' e = readIORef stRef >>= \st ->
                            handler runAlgebra st e

           listener <- syncCallback1 ContinueAsync handler'
           attachHandler n listener

           pure (detachHandler n listener, stRef)

    update st _ intSt@(_, stRef) =
        do writeIORef stRef st
           pure intSt

    finish = do (release, _) <- ask
                liftIO release


on :: forall evt algebra state parentAlgebra.
      FromEvent evt =>
      EventName Element evt -> ((forall a m. MonadIO m => algebra a -> m a) -> state -> EventM Element evt ())
   -> Attribute (IO (), IORef state) state algebra parentAlgebra
on (EventName evtName) handler =
    Attribute set update finish
  where
    set :: RunAlgebra algebra -> state -> Node -> IO (IO (), IORef state)
    set runAlgebra st n =
        do stRef <- liftIO (newIORef st)
           listener <- eventListenerNew (handler' stRef runAlgebra)

           addEventListener (toEventTarget n) evtName (Just listener) False

           let finish = do removeEventListener (toEventTarget n) evtName (Just listener) False
                           eventListenerRelease listener

           pure (finish, stRef)

    handler' :: IORef state -> RunAlgebra algebra -> Event -> IO ()
    handler' stRef runAlgebra evt =
        do st <- readIORef stRef
           Just target <- getTarget evt
           let runAlgebra' :: forall a m. MonadIO m => algebra a -> m a
               runAlgebra' x = liftIO (runAlgebra x)
           runReaderT (handler runAlgebra' st) =<< fromEvent evt

    update st _ intSt@(_, stRef) =
        do writeIORef stRef st
           pure intSt

    finish = do (release, _) <- ask
                liftIO release

raw_ :: (st -> JSString) -> Snippet Node out st algebra parentAlgebra
raw_ mkHtml = Snippet createUnder updateElem finish
    where
      createUnder _ st insertPos =
          do el <- mkEl (mkHtml st)

             insertPos' <- insertAtPos insertPos (toNode el)

             pure (ConstructedSnippet mempty mempty
                                      insertPos'
                                      (DOMInsertPos (toNode el) Nothing)
                                      el)

      updateElem st insertPos el =
          do finish' el

             el' <- mkEl (mkHtml st)
             insertPos' <- insertAtPos insertPos (toNode el')

             pure (ConstructedSnippet mempty mempty
                                      insertPos'
                                      (DOMInsertPos (toNode el') Nothing) el')

      finish = do el <- ask
                  liftIO (finish' el)
      finish' el = do parent <- getParentNode el
                      case parent of
                        Just parent ->
                            do removeChild parent (Just el)
                               pure ()
                        _ -> pure ()

      mkEl html =
          do Just document <- currentDocument
             Just spanEl <- createElement document (Just "span" :: Maybe JSString)

             setInnerHTML spanEl (Just html)

             children <- getChildNodes spanEl
             childCount <- maybe (pure 0) getLength children
             case (children, childCount) of
               (_, 0) -> pure (toNode spanEl)
               (Nothing, _) -> pure (toNode spanEl)
               (Just children, count) ->
                   do child <- item children 0
                      pure (fromMaybe (toNode spanEl) child)

el :: JSString -> Snippet Element out st algebra parentAlgebra
el tagName = Snippet createUnder updateElem finish
  where
    createUnder _ _ insertPos =
      do Just document <- liftIO currentDocument

         Just el <- createElement document (Just tagName)

         insertPos' <- liftIO (insertAtPos insertPos (toNode el))
         pure (ConstructedSnippet mempty mempty
                                  insertPos' (DOMInsertPos (toNode el) Nothing)
                                  el)

    updateElem _ (DOMInsertPos parent _) el=
      pure (ConstructedSnippet mempty mempty
                               (DOMInsertPos parent (Just (toNode el)))
                               (DOMInsertPos (toNode el) Nothing)
                               el)

    finish =
      do el <- ask

         parent <- getParentNode el
         case parent of
           Just parent ->
               do removeChild parent (Just el)
                  pure ()
           _ -> pure ()

text :: JSString -> Snippet Node out st algebra parentAlgebra
text str = Snippet createUnder updateElem finish
  where
    createUnder _ _ insertPos =
      do Just document <- liftIO currentDocument

         Just el <- createTextNode document str

         insertPos' <- liftIO (insertAtPos insertPos (toNode el))
         pure (ConstructedSnippet mempty mempty
                                  insertPos' (DOMInsertPos (toNode el) Nothing) (toNode el))

    updateElem _ (DOMInsertPos parent _) el =
      pure (ConstructedSnippet mempty mempty
                               (DOMInsertPos parent (Just (toNode el))) (DOMInsertPos (toNode el) Nothing)
                               el)

    finish =
      do el <- ask

         parent <- getParentNode el
         case parent of
           Just parent ->
               do removeChild parent (Just el)
                  pure ()
           Nothing -> pure ()

dyn = dyn' id
dynText = dyn' textToJSString

dyn' :: Eq s => (s -> JSString) -> (state -> s) -> Snippet (Text :++ s) out state algebra parentAlgebra
dyn' toString fromState = Snippet createUnder updateElem finish
  where
    createUnder _ st insertPos =
        do Just document <- liftIO currentDocument

           let str = toString strInt
               strInt = fromState st
           Just el <- createTextNode document str

           insertPos' <- liftIO (insertAtPos insertPos (toNode el))

           pure (ConstructedSnippet mempty mempty
                                    insertPos'
                                    (DOMInsertPos (toNode el) Nothing)
                                    (el :++ strInt))

    updateElem st (DOMInsertPos parent _) (txt :++ str) =
        do let str' = toString stInt
               stInt = fromState st
           when (str /= stInt) $
                do setNodeValue txt (Just str')
           pure (ConstructedSnippet mempty mempty
                                    (DOMInsertPos parent (Just (toNode txt)))
                                    (DOMInsertPos (toNode txt) Nothing)
                                    (txt :++ stInt))

    finish =
        do (txt :++ _) <- ask
           Just parent <- getParentNode txt
           removeChild parent (Just txt)
           pure ()

project_ :: (st -> st')
         -> Snippet intSt out st' algebra parentAlgebra
         -> Snippet intSt out st algebra parentAlgebra
project_ f (Snippet createElem updateElem finishElem) =
    Snippet (\run st pos -> createElem run (f st) pos)
            (\st pos intSt -> updateElem (f st) pos intSt)
            finishElem

enum_ :: forall state ix intSt algebra parentAlgebra out.
         (Enum ix, Ord ix, Show ix) =>
         (state -> (ix, ix))
      -> Snippet intSt out (Embedded ix state ix) algebra parentAlgebra
      -> Snippet (RunAlgebraWrapper algebra, ix, ix, [intSt]) out state algebra parentAlgebra
enum_ mkBounds (Snippet createItem updateItem finishItem) =
    Snippet createItems updateItems finishItems
  where
    createItems :: RunAlgebra algebra -> state -> SnippetConstructor (RunAlgebraWrapper algebra, ix, ix, [intSt]) out
    createItems runAlgebra state pos =
        do let (start, end) = mkBounds state

           res <- createAll runAlgebra state start (start, end) (ConstructedSnippet mempty mempty pos pos id)
           pure (res { constructedState = (RunAlgebraWrapper runAlgebra, start, end, constructedState res []) })

    createAll :: RunAlgebra algebra -> state -> ix -> (ix, ix)
              -> ConstructedSnippet ([intSt] -> [intSt]) out
              -> IO (ConstructedSnippet ([intSt] -> [intSt]) out)
    createAll runAlgebra state !ix (start, end) a
        | start > end || ix > end =
            pure a
    createAll runAlgebra state !ix bounds@(start, end) (ConstructedSnippet mkOut scheduled siblingPos _ a) =
        do ConstructedSnippet itemMkOut itemScheduled siblingPos' childPos' itemIntSt <-
               createItem runAlgebra (Embedded state ix ix) siblingPos
           createAll runAlgebra state (succ ix) bounds
                     (ConstructedSnippet (mkOut <> itemMkOut) (scheduled <> itemScheduled)
                                         siblingPos' childPos' (a . (itemIntSt :)))

    updateAll :: state -> ix -> [intSt] -> ConstructedSnippet ([intSt] -> [intSt]) out
              -> IO (ConstructedSnippet ([intSt] -> [intSt]) out)
    updateAll _ !ix [] a = pure a
    updateAll state !ix (item:items) (ConstructedSnippet mkOut scheduled siblingPos _ a) =
        do ConstructedSnippet itemMkOut itemScheduled siblingPos' childPos' itemIntSt' <-
               updateItem (Embedded state ix ix) siblingPos item
           updateAll state (succ ix) items (ConstructedSnippet (mkOut <> itemMkOut) (scheduled <> itemScheduled)
                                                               siblingPos' childPos'
                                                               (a . (itemIntSt' :)))

    updateItems :: state -> SnippetUpdater (RunAlgebraWrapper algebra, ix, ix, [intSt]) out
    updateItems state pos (runAlgebra@(RunAlgebraWrapper runAlgebra_), oldStart, oldEnd, intSts) =
        do let (newStart, newEnd) = mkBounds state

               newStartIdx = fromEnum newStart
               newEndIdx   = fromEnum newEnd

               oldStartIdx = fromEnum oldStart
               oldEndIdx   = fromEnum oldEnd

               ( (removeFromBeginning, addToBeginning),
                 (removeFromEnd,       addToEnd) )
                 | newEndIdx < newStartIdx =
                     ( (length intSts, (succ newStart, newStart)), (0, (succ newEnd, newEnd)) )
                 | newEndIdx < oldStartIdx = -- scrolled up all the way
                     ( (length intSts, (newStart, newEnd)), (0, (succ newEnd, newEnd)) )
                 | newStartIdx > oldEndIdx = -- scrolled down all the way
                     ( (length intSts, (newStart, newEnd)), (0, (succ newEnd, newEnd)) )
                 | otherwise =
                     let beginning | newStartIdx < oldStartIdx = ( 0, (newStart, pred oldStart) )
                                   | otherwise = ( newStartIdx - oldStartIdx, (succ newStart, newStart) )
                         end       | newEndIdx > oldEndIdx = ( 0, (succ oldEnd, newEnd) )
                                   | otherwise = ( oldEndIdx - newEndIdx, (succ newEnd, newEnd) )
                     in (beginning, end)

               intStsLength = length intSts
               (intSts', removedFromEnd) = splitAt (intStsLength - removeFromEnd) intSts
               (removedFromBeginning, preservedSts) = splitAt removeFromBeginning intSts'

               preservedCount = intStsLength - removeFromBeginning - removeFromEnd
               preservedStart = toEnum (oldStartIdx + removeFromBeginning)

           forM_ (removedFromBeginning <> removedFromEnd) $ \st ->
               liftIO (runReaderT finishItem st)

           beginning <- createAll runAlgebra_ state (fst addToBeginning) addToBeginning (ConstructedSnippet mempty mempty pos pos id)
           updated <- updateAll state preservedStart preservedSts beginning
           end <- createAll runAlgebra_ state (fst addToEnd) addToEnd updated

           pure (end { constructedState = (runAlgebra, newStart, newEnd, constructedState end []) })

    finishItems =
      do (_, _, _, intSts) <- ask
         lift . forM_ intSts $ \itemIntSt ->
             runReaderT finishItem itemIntSt

repeat_ :: forall state current intSt algebra parentAlgebra out.
          (state -> [current]) -> Snippet intSt out (Embedded Int state current) algebra parentAlgebra
       -> Snippet (RunAlgebraWrapper algebra, [intSt]) out state algebra parentAlgebra
repeat_ mkCurrent (Snippet createItem updateItem finishItem) =
    Snippet createItems updateItems finishItems
  where
    createItems :: RunAlgebra algebra -> state -> SnippetConstructor (RunAlgebraWrapper algebra, [intSt]) out
    createItems runAlgebra state siblingPos =
        do let current = mkCurrent state
           createAll runAlgebra state 0 current (ConstructedSnippet mempty mempty siblingPos siblingPos id)

    createAll :: RunAlgebra algebra -> state -> Int -> [current] -> ConstructedSnippet ([intSt] -> [intSt]) out
              -> IO (ConstructedSnippet (RunAlgebraWrapper algebra, [intSt]) out)
    createAll runAlgebra _ !ix [] (ConstructedSnippet mkOut scheduled siblingPos' childPos a) =
        pure (ConstructedSnippet mkOut scheduled siblingPos' childPos (RunAlgebraWrapper runAlgebra, a []))
    createAll runAlgebra state !ix (item:items) (ConstructedSnippet mkOut scheduled siblingPos' _ a) =
        do ConstructedSnippet itemMkOut itemScheduled siblingPos'' childPos' itemIntSt <-
               createItem runAlgebra (Embedded state item ix) siblingPos'
           createAll runAlgebra state (ix + 1) items (ConstructedSnippet (mkOut <> itemMkOut) (scheduled <> itemScheduled) siblingPos'' childPos' (a . (itemIntSt:)))

    updateAll _ !_ [] _ a = pure a
    updateAll _ !_ _ [] a = pure a
    updateAll state !ix (current:currents) (itemIntSt:itemIntSts) (ConstructedSnippet mkOut scheduled siblingPos _ a) =
        do ConstructedSnippet itemMkOut itemScheduled siblingPos' childPos' itemIntSt' <-
               updateItem (Embedded state current ix) siblingPos itemIntSt

           updateAll state (ix + 1) currents itemIntSts
                     (ConstructedSnippet (mkOut <> itemMkOut) (scheduled <> itemScheduled)
                                         siblingPos' childPos'
                                         (a . (itemIntSt':)))

    updateItems :: state -> SnippetUpdater (RunAlgebraWrapper algebra, [intSt]) out
    updateItems state pos (runAlgebra@(RunAlgebraWrapper runAlgebra_), intSt) =
        do let current  = mkCurrent state
               (intSt', toRemove) = splitAt (length current) intSt
               toAdd = drop (length intSt') current


           forM_ toRemove $ \intSt ->
               liftIO (runReaderT finishItem intSt)

           createAll runAlgebra_ state (length intSt') toAdd =<<
            updateAll state 0 current intSt' (ConstructedSnippet mempty mempty pos pos id)

    finishItems =
        do (_, intSts) <- ask
           forM_ intSts $ \itemIntSt ->
               lift (runReaderT finishItem itemIntSt)

attrKeyedUpdates_ :: forall key internalSt st algebra parentAlgebra.
                     Eq key => (st -> key)
                  -> Attribute internalSt key algebra parentAlgebra
                  -> Attribute (key, internalSt) st algebra parentAlgebra
attrKeyedUpdates_ mkKey (Attribute set update finish) = Attribute set' update' finish'
    where
      set' :: RunAlgebra algebra -> st -> Node -> IO (key, internalSt)
      set' runAlgebra st node =
          do let key = mkKey st
             x <- set runAlgebra key node
             pure (key, x)

      update' st node oldIntSt@(oldKey, x)=
          let newKey = mkKey st
          in if oldKey /= newKey
             then do x' <- update newKey node x
                     pure (newKey, x')
             else pure oldIntSt

      finish' = do (_, x) <- ask
                   lift (runReaderT finish x)

keyedUpdates_ :: forall state internalSt key out algebra parentAlgebra.
                 Eq key => (state -> key)
              -> Snippet internalSt out state algebra parentAlgebra
              -> Snippet (key, DOMInsertPos, DOMInsertPos, Endo out, internalSt) out state algebra parentAlgebra
keyedUpdates_ mkKey (Snippet createUnder updateElem finish) =
    Snippet createUnder' updateElem' finish'
  where
    createUnder' :: RunAlgebra algebra -> state
                 -> SnippetConstructor (key, DOMInsertPos, DOMInsertPos, Endo out, internalSt) out
    createUnder' update st siblingPos =
        do ConstructedSnippet mkOut scheduled siblingPos' pos internalSt <-
               createUnder update st siblingPos

           pure (ConstructedSnippet mkOut scheduled siblingPos' pos
                                    (mkKey st, pos, siblingPos', mkOut, internalSt))

    updateElem' st siblingPos oldSt@(oldKey, oldPos, oldSiblingPos, oldMkOut, oldInternalSt) =
        let newKey = mkKey st
        in if oldKey == newKey
           then pure (ConstructedSnippet oldMkOut mempty
                                         oldSiblingPos oldPos
                                         oldSt)
           else do ConstructedSnippet mkOut scheduled siblingPos' pos internalSt' <-
                       updateElem st siblingPos oldInternalSt
                   pure (ConstructedSnippet mkOut scheduled siblingPos' pos
                                            (newKey, pos, siblingPos', mkOut, internalSt'))

    finish' = do (_, _, _, _, st) <- ask
                 lift (runReaderT finish st)

switch_ :: forall state key out algebra parentAlgebra.
           Eq key => (state -> key)
        -> (state -> key -> SomeSnippet out state algebra parentAlgebra)
        -> Snippet (key, RenderedSnippet out state, RunAlgebraWrapper algebra) out state algebra parentAlgebra
switch_ mkKey mkComponent =
    Snippet createUnder' updateElem' finish'
  where createUnder' :: RunAlgebra algebra -> state
                     -> SnippetConstructor (key, RenderedSnippet out state, RunAlgebraWrapper algebra) out
        createUnder' update st pos =
            let initialKey = mkKey st
            in case mkComponent st initialKey of
                 SomeSnippet (Snippet createUnder updateElem finish) ->
                     do ConstructedSnippet mkOut after siblingPos childPos intSt <-
                            createUnder update st pos

                        let intSt' = RenderedSnippet intSt updateElem finish
                        pure (ConstructedSnippet mkOut after siblingPos childPos
                                                 (initialKey, intSt', RunAlgebraWrapper update))

        updateElem' st siblingPos (oldKey, rendered, RunAlgebraWrapper update) =
            let !key = mkKey st
            in case rendered of
                 RenderedSnippet intSt updateElem finish ->
                     if key == oldKey
                     then do ConstructedSnippet mkOut scheduled siblingPos' childPos intSt' <-
                                 updateElem st siblingPos intSt
                             pure (ConstructedSnippet mkOut scheduled siblingPos' childPos
                                                      (key, RenderedSnippet intSt' updateElem finish, RunAlgebraWrapper update))
                     else do runReaderT finish intSt
                             case mkComponent st key of
                               SomeSnippet (Snippet createUnder updateElem finish) ->
                                   do ConstructedSnippet mkOut after siblingPos' childPos intSt <-
                                          createUnder update st siblingPos
                                      pure (ConstructedSnippet mkOut after siblingPos' childPos
                                                               (key, RenderedSnippet intSt updateElem finish, RunAlgebraWrapper update))

        finish' = do (_, RenderedSnippet st _ finish, _) <- ask
                     lift (runReaderT finish st)

cond_ :: forall state childEl out algebra parentAlgebra.
         (state -> Bool) -> Snippet childEl out state algebra parentAlgebra
      -> Snippet (Maybe childEl, RunAlgebraWrapper algebra) out state algebra parentAlgebra
cond_ cond template =
    guarded_ (\s -> if cond s then Just s else Nothing)
             (project_ (\(Embedded _ s _) -> s) template)

guarded_ :: forall state state' childEl out algebra parentAlgebra.
            (state -> Maybe state')
         -> Snippet childEl out (Embedded () state state') algebra parentAlgebra
         -> Snippet (Maybe childEl, RunAlgebraWrapper algebra) out state algebra parentAlgebra
guarded_ check (Snippet createUnder updateElem finish) =
    Snippet createUnder' updateElem' finish'
  where createUnder' :: RunAlgebra algebra -> state -> SnippetConstructor (Maybe childEl, RunAlgebraWrapper algebra) out
        createUnder' update st siblingPos =
            case check st of
              Just st' ->
                  do ConstructedSnippet mkOut scheduled siblingPos' childPos intSt <-
                         createUnder update (Embedded st st' ()) siblingPos
                     pure (ConstructedSnippet mkOut scheduled siblingPos' childPos
                                              (Just intSt, RunAlgebraWrapper update))
              Nothing -> pure (ConstructedSnippet mempty mempty
                                                  siblingPos siblingPos
                                                  (Nothing, RunAlgebraWrapper update))

        updateElem' st pos (intSt, RunAlgebraWrapper update) =
            case (check st, intSt) of
              (Nothing, Nothing) ->
                  pure (ConstructedSnippet mempty mempty pos pos (intSt, RunAlgebraWrapper update))
              (Just st', Nothing) ->
                  do ConstructedSnippet mkOut scheduled siblingPos' childPos intSt' <-
                         createUnder update (Embedded st st' ()) pos
                     pure (ConstructedSnippet mkOut scheduled siblingPos' childPos
                                              (Just intSt', RunAlgebraWrapper update))
              (Nothing, Just childSt) ->
                  do runReaderT finish childSt
                     pure (ConstructedSnippet mempty mempty pos pos (Nothing, RunAlgebraWrapper update))
              (Just st', Just childSt) ->
                  do ConstructedSnippet mkOut scheduled siblingPos' childPos intSt' <-
                         updateElem (Embedded st st' ()) pos childSt
                     pure (ConstructedSnippet mkOut scheduled siblingPos' childPos
                                              (Just intSt', RunAlgebraWrapper update))

        finish' =
            do (intSt, _) <- ask
               case intSt of
                 Nothing -> pure ()
                 Just intSt ->
                     lift (runReaderT finish intSt)

(|++) :: forall left right st algebra parentAlgebra.
         Attribute left st algebra parentAlgebra
      -> Attribute right st algebra parentAlgebra
      -> Attribute (left :++ right) st algebra parentAlgebra
Attribute setLeft updateLeft finishLeft |++ Attribute setRight updateRight finishRight =
    Attribute set update finish
  where
    set :: RunAlgebra algebra -> st -> Node -> IO (left :++ right)
    set runAlgebra st node =
        do left <- setLeft runAlgebra st node
           right <- setRight runAlgebra st node
           pure (left :++ right)

    update st node (left :++ right) =
        do left' <- updateLeft st node left
           right' <- updateRight st node right
           pure (left' :++ right')

    finish = do (left :++ right) <- ask
                lift (runReaderT finishLeft left)
                lift (runReaderT finishRight right)

(|<>) :: forall leftEl rightEl state algebra parentAlgebra out.
         Snippet leftEl out state algebra parentAlgebra
      -> Snippet rightEl out state algebra parentAlgebra
      -> Snippet (leftEl :++ rightEl) out state algebra parentAlgebra
Snippet createLeft updateLeft finishLeft |<> Snippet createRight updateRight finishRight =
  Snippet createUnder updateElem finish
  where createUnder :: RunAlgebra algebra -> state -> SnippetConstructor (leftEl :++ rightEl) out
        createUnder runAlgebra st siblingPos =
            do ConstructedSnippet leftOut leftScheduled siblingPos' _ !leftIntSt <-
                   createLeft runAlgebra st siblingPos
               ConstructedSnippet rightOut rightScheduled siblingPos'' childPos !rightIntSt <-
                   createRight runAlgebra st siblingPos'
               pure (ConstructedSnippet (leftOut <> rightOut) (leftScheduled <> rightScheduled)
                                        siblingPos'' childPos (leftIntSt :++ rightIntSt))

        updateElem st siblingPos (leftIntSt :++ rightIntSt) =
            do ConstructedSnippet leftOut leftScheduled siblingPos' _ !leftIntSt' <-
                   updateLeft st siblingPos leftIntSt
               ConstructedSnippet rightOut rightScheduled siblingPos'' childPos !rightIntSt' <-
                   updateRight st siblingPos' rightIntSt
               pure (ConstructedSnippet (leftOut <> rightOut) (leftScheduled <> rightScheduled)
                                        siblingPos'' childPos (leftIntSt' :++ rightIntSt'))

        finish =
            do (leftSt :++ rightSt) <- ask
               lift (runReaderT finishLeft leftSt)
               lift (runReaderT finishRight rightSt)

{-# INLINE (|-*) #-}
(|-*) :: Snippet parentEl out state algebra parentAlgebra
      -> SomeSnippet out state algebra parentAlgebra
      -> Snippet (parentEl :++ RenderedSnippet out state) out state algebra parentAlgebra
parent |-* child = parent |- someSnippet_ child

{-# INLINE (|-) #-}
(|-) :: forall parentEl childEl state algebra parentAlgebra out.
        Snippet parentEl out state algebra parentAlgebra
     -> Snippet childEl out state algebra parentAlgebra
     -> Snippet (parentEl :++ childEl) out state algebra parentAlgebra
Snippet createParent updateParent finishParent |- Snippet createChild updateChild finishChild =
  Snippet createUnder' updateElem' finish'
  where createUnder' :: RunAlgebra algebra -> state -> SnippetConstructor (parentEl :++ childEl) out
        createUnder' runAlgebra st pos =
          do ConstructedSnippet parentOut parentScheduled
                                siblingPos parentChildPos !parentIntSt <-
                                    createParent runAlgebra st pos
             ConstructedSnippet childOut childScheduled
                                childPos' _ !childIntSt <-
                                    createChild runAlgebra st parentChildPos
             pure (ConstructedSnippet (parentOut <> childOut) (parentScheduled <> childScheduled)
                                      siblingPos childPos' (parentIntSt :++ childIntSt))

        updateElem' st siblingInsertPos (parentIntSt :++ childIntSt) =
          do ConstructedSnippet parentOut parentScheduled
                                siblingInsertPos' parentChildPos !parentIntSt' <-
                                    updateParent st siblingInsertPos parentIntSt
             ConstructedSnippet childOut childScheduled
                                childPos' _ !childIntSt' <-
                                    updateChild st parentChildPos childIntSt
             pure (ConstructedSnippet (parentOut <> childOut) (parentScheduled <> childScheduled)
                                      siblingInsertPos' childPos' (parentIntSt' :++ childIntSt'))

        finish' =
          do (parentSt :++ childSt) <- ask

             lift (runReaderT finishParent parentSt)
             lift (runReaderT finishChild childSt)
infixl 1 |-, |-*

{-# INLINE (|+) #-}
(|+) :: forall elSt attrSt state algebra parentAlgebra out.
        Snippet elSt out state algebra parentAlgebra
     -> Attribute attrSt state algebra parentAlgebra
     -> Snippet (elSt :++ attrSt) out state algebra parentAlgebra
Snippet createUnder updateElem finishElem |+ Attribute setAttr updateAttr finishAttr =
  Snippet createUnder' updateElem' finish'
  where createUnder' :: RunAlgebra algebra -> state -> SnippetConstructor (elSt :++ attrSt) out
        createUnder' runAlgebra st insertPos =
          do ConstructedSnippet elOut elAfter siblingPos childPos !elIntSt <-
                 createUnder runAlgebra st insertPos
             !attrSt <- setAttr runAlgebra st (insertPosParent childPos)

             pure (ConstructedSnippet elOut elAfter
                                      siblingPos childPos (elIntSt :++ attrSt))

        updateElem' st insertPos (elSt :++ attrSt) =
          do ConstructedSnippet elOut elAfter siblingPos childPos !elSt' <-
                 updateElem st insertPos elSt
             !attrSt' <- updateAttr st (insertPosParent childPos) attrSt

             pure (ConstructedSnippet elOut elAfter siblingPos childPos (elSt' :++ attrSt'))

        finish' =
          do (elemSt :++ attrSt) <- ask

             lift (runReaderT finishElem elemSt)
             lift (runReaderT finishAttr attrSt)

captured_ :: forall internalState out state algebra parentAlgebra.
             (internalState -> out -> out)
          -> Snippet internalState out state algebra parentAlgebra
          -> Snippet internalState out state algebra parentAlgebra
captured_ modOut (Snippet createUnder updateElem finish) =
    Snippet createUnder' updateElem' finish
    where createUnder' :: RunAlgebra algebra -> state -> SnippetConstructor internalState out
          createUnder' run st pos =
              do res <- createUnder run st pos
                 pure res { constructedSnippetOut = constructedSnippetOut res <>
                                                    Endo (modOut (constructedState res)) }
          updateElem' st pos intSt =
              do res <- updateElem st pos intSt
                 pure res { constructedSnippetOut = constructedSnippetOut res <>
                                                    Endo (modOut (constructedState res)) }

someSnippet_ :: forall out state algebra parentAlgebra.
                SomeSnippet out state algebra parentAlgebra
             -> Snippet (RenderedSnippet out state) out state algebra parentAlgebra
someSnippet_ (SomeSnippet (Snippet createUnder updateElem finish)) =
    Snippet createUnder' updateElem' finish'
  where
    createUnder' :: RunAlgebra algebra -> state -> SnippetConstructor (RenderedSnippet out state) out
    createUnder' update st pos =
        do ConstructedSnippet mkOut scheduled siblingPos childPos intSt <- createUnder update st pos
           pure (ConstructedSnippet mkOut scheduled siblingPos childPos
                                    (RenderedSnippet intSt updateElem finish))

    updateElem' st siblingPos (RenderedSnippet intSt updateElem finish) =
        do ConstructedSnippet mkOut scheduled siblingPos' childPos intSt' <-
               updateElem st siblingPos intSt
           pure (ConstructedSnippet mkOut scheduled siblingPos' childPos
                                    (RenderedSnippet intSt' updateElem finish))

    finish' :: ReaderT (RenderedSnippet out state) IO ()
    finish' = do RenderedSnippet intSt _ finish <- ask
                 lift (runReaderT finish intSt)

mount_ :: forall childAlgebra out st algebra parentAlgebra.
          (MonadIO algebra, RawIO algebra) =>
          (st -> EmbeddedAlgebraWrapper childAlgebra algebra -> out -> out) -> (st -> Component childAlgebra algebra)
       -> Snippet (MountedComponent childAlgebra algebra) out st algebra parentAlgebra
mount_ setChild mkComponent = Snippet createUnder updateElem finish
    where createUnder :: RunAlgebra algebra -> st -> SnippetConstructor (MountedComponent childAlgebra algebra) out
          createUnder update st siblingPos =
            case mkComponent st of
              Component { componentTemplate = componentTemplate@(Snippet { .. })
                        , .. } -> do
                 stVar  <- liftIO newEmptyMVar
                 outVar <- liftIO (newIORef (error "outVar not set"))
                 intStVar <- liftIO (newIORef (error "intStVar not set"))
                 doneVar <- liftIO (newIORef False)
                 siblingVar <- liftIO newEmptyMVar

                 isDirtyV <- liftIO (newIORef False)
                 Just window <- liftIO currentWindow

                 let redraw _ = do putStrLn "redraw mount_"
                                   isDone <- readIORef doneVar
                                   scheduled <- if not isDone then
                                                    do --putStrLn "redraw after isDone 1"
                                                       atomicWriteIORef isDirtyV False

                                                       (st, intSt) <- bracket (takeMVar stVar) (putMVar stVar) $ \st ->
                                                                      (st,) <$> readIORef intStVar
                                                       (insPos, _, childPos) <- takeMVar siblingVar
                                                       ConstructedSnippet (Endo mkOut) scheduled insPos' childPos !intSt' <-
                                                           snippetUpdateElem st insPos intSt

                                                       atomicWriteIORef intStVar intSt'
                                                       putMVar siblingVar (insPos, insPos', childPos)

                                                       let !out = mkOut componentEmptyOut
                                                       atomicWriteIORef outVar out
--                                                       putStrLn "redraw after isDone 3"
                                                       pure (runAfterAction scheduled out)
                                                  else do
--                                                    putStrLn "redraw after isDone 2"
                                                    atomicWriteIORef isDirtyV False
                                                    pure (pure ())
                                   putStrLn "redraw after run scheduled"
                                   scheduled
                                   putStrLn "done redraw"

--                 redrawCallback <- newRequestAnimationFrameCallback redraw

                 let intSt = MountedComponent stVar intStVar outVar siblingVar
                                              componentEmptyOut (EmbeddedAlgebraWrapper runAlgebra'') finish
                                              componentRunAlgebra componentTemplate

                     finish = do isDone <- atomicModifyIORef doneVar (\isDone -> (True, isDone))
                                 when (not isDone) $
                                   do --redrawState <- readMVar redrawStateVar
                                      -- case redrawState of
                                      --   Nothing -> pure ()
                                      --   Just id -> cancelAnimationFrame window id

                                      -- let RequestAnimationFrameCallback cb = redrawCallback
                                      -- releaseCallback cb

                                      (st, intSt) <- bracket (takeMVar stVar) (putMVar stVar) $ \st ->
                                                     (st,) <$> readIORef intStVar
                                      runReaderT snippetFinish intSt

                     runAlgebra'' :: forall a. childAlgebra a -> algebra a
                     runAlgebra'' a = do --liftIO $ putStrLn "runAlgebra''"
                                         (isDone, st, intSt, out, oldStNm) <-
                                             rawIO $
                                             do isDone <- readIORef doneVar
                                                st <- takeMVar stVar
                                                (isDone,st,,,) <$> readIORef intStVar <*> readIORef outVar <*> makeStableName st

                                         --liftIO $ putStrLn "Got state"
                                         (x, !st') <- componentRunAlgebra (EnterExit (\(!st) -> rawIO (putMVar stVar st)) (rawIO (takeMVar stVar))) st out a

                                         rawIO $
                                           if isDone
                                           then putMVar stVar st
                                           else do putMVar stVar st'

                                                   newStNm <- makeStableName st'
                                                   when (oldStNm /= newStNm) $ do
                                                     wasDirty <- atomicModifyIORef isDirtyV (\isDirty -> (True, isDirty))
                                                     when (not wasDirty) (requestAnimationFrameHs redraw)
                                         pure x

                     runAlgebra' :: forall a. childAlgebra a -> IO a
                     runAlgebra' a = update (runAlgebra'' a)

                 ConstructedSnippet (Endo mkOut) scheduled siblingPos' childPos compIntSt <-
                     snippetCreateUnder runAlgebra' componentStateInitial siblingPos
        --             lift (lift (runWriterT (runStateT (snippetCreateUnder runAlgebra' componentStateInitial) siblingPos)))

                 atomicWriteIORef intStVar compIntSt

                 let !initialOut = mkOut componentEmptyOut
                 atomicWriteIORef outVar initialOut

                 putMVar stVar componentStateInitial
                 putMVar siblingVar (siblingPos, siblingPos', childPos)

                 pure (ConstructedSnippet (Endo (setChild st (EmbeddedAlgebraWrapper runAlgebra'')))
                                          (AfterAction [ \_ -> runAlgebra' (componentOnConstruct runAlgebra')
                                                       , \_ -> runAfterAction scheduled initialOut ])
                                          siblingPos' childPos intSt)

          updateElem st insPos mc@MountedComponent { .. } =
              do (_, insPos', childPos) <- liftIO (readMVar mountedInsPosV)

                 pure (ConstructedSnippet (Endo (setChild st mountedAlgebraWrapper))
                                          mempty insPos' childPos mc)

          finish =
              do MountedComponent { .. } <- ask
                 liftIO mountedFinish

comp :: MonadIO parentAlgebra =>
        state -> out -> (forall a. EnterExit state parentAlgebra -> state -> out -> algebra a -> parentAlgebra (a, state))
     -> (RunAlgebra algebra -> algebra ())
     -> Snippet internalState out state algebra parentAlgebra -> Component algebra parentAlgebra
comp = Component

statefulComp :: MonadIO parentAlgebra =>
                state -> out -> (RunAlgebra (EnterExitT state out parentAlgebra) -> EnterExitT state out parentAlgebra ())
             -> Snippet internalState out state (EnterExitT state out parentAlgebra) parentAlgebra
             -> Component (EnterExitT state out parentAlgebra) parentAlgebra
statefulComp st out = comp st out (\enterExit st out a -> runEnterExitT a enterExit out st)

emptyComp :: MonadIO parentAlgebra => Component parentAlgebra parentAlgebra
emptyComp = comp () () (\_ st _ a -> do { x <- a; return (x, st); }) (\_ -> return ()) (span_)  -- TODO this can probably be an empty element

emptySnippet :: Snippet () out state algebra parentAlgebra
emptySnippet = Snippet (\_ _ pos -> pure (ConstructedSnippet mempty mempty pos pos ()))
                       (\_ pos () -> pure (ConstructedSnippet mempty mempty pos pos ())) (return ())

mountComponent :: Element -> Component algebra IO -> IO ()
mountComponent el (Component st emptyOut runAlgebra onCreate (Snippet createTemplate updateTemplate finishTemplate :: Snippet intSt st out algebra IO))  =
  do stVar <- newEmptyMVar
     intStVar <- newIORef (error "intStVar not set")
     outVar <- newIORef (error "outVar not set")
     syncVar <- newMVar ()

     Just window <- currentWindow

     isDirtyV <- newIORef False
     let redraw _ = do putStrLn "redraw mountcomponent"
                       atomicWriteIORef isDirtyV False
                       (st, intSt) <- bracket (takeMVar stVar) (putMVar stVar) $ \st ->
                                      (st,) <$> readIORef intStVar
--                       (st, intSt) <- takeMVar stVar
                       --putStrLn "redraw mountcomponent 1"
                       ConstructedSnippet (Endo mkOut) scheduled _ _ intSt' <-
                           updateTemplate st (DOMInsertPos (toNode el) Nothing) intSt
                       --putStrLn "redraw mountcomponent 2"
                       atomicWriteIORef intStVar intSt'
--                       putMVar stVar (st, intSt')
                       --putStrLn "redraw mountcomponent 3"
                       let out' = mkOut emptyOut
                       atomicWriteIORef outVar out'
                       putStrLn "Running mountcomponent afteraction"
                       runAfterAction scheduled out'
                       putStrLn "Done redraw"

--     redrawCallback <- newRequestAnimationFrameCallback redraw

     let runAlgebra' :: forall a. algebra a -> IO a
         runAlgebra' a =
--           putStrLn "Run algebra mount component"
--           bracket (takeMVar syncVar) (putMVar syncVar) $ \_ ->
             do (x, shouldRedraw) <- modifyMVar stVar $ \st ->
                     do out <- readIORef outVar
                        intSt <- readIORef intStVar
                        oldStNm <- makeStableName st
                        (x, !st') <- runAlgebra (EnterExit (putMVar stVar) (takeMVar stVar)) st out a
                        newStNm <- makeStableName st'
                        pure (st', (x, oldStNm /= newStNm))

--                putStrLn ("Mount component should redraw: " <> show shouldRedraw)
                when shouldRedraw scheduleRedraw

                pure x
         scheduleRedraw = do
           wasDirty <- atomicModifyIORef isDirtyV (\isDirty -> (True, isDirty))
           when (not wasDirty) (requestAnimationFrameHs redraw)

     ConstructedSnippet (Endo mkOut) scheduled _ _ intSt <-
         createTemplate runAlgebra' st (DOMInsertPos (toNode el) Nothing)

     atomicWriteIORef intStVar intSt

     let !initialOut = mkOut emptyOut
     atomicWriteIORef outVar initialOut

     putMVar stVar st

     putStrLn "Start create actions"
     runAlgebra' (onCreate runAlgebra')
     runAfterAction scheduled initialOut
     putStrLn "Done create action"

     pure ()

addStylesheet :: JSString -> IO ()
addStylesheet loc =
    do Just document <- currentDocument
       Just head <- getHead document

       Just link <- createElement document (Just "link" :: Maybe JSString)
       setAttribute link ("rel" :: JSString) ("stylesheet" :: JSString)
       setAttribute link ("type" :: JSString) ("text/css" :: JSString)
       setAttribute link ("href" :: JSString) loc

       appendChild head (Just link)
       pure ()

-- setCharset :: JSString -> IO ()
-- setCharset name =
--     do Just document <- currentDocument
--        Just head <- getHead document

--        Just meta <- createElement document (Just "meta")
--        setAttribute meta ("charset" :: JSString) name

--        appendChild head (Just meta)
--        pure ()

-- * Elements

a_ = el "a"
p_ = el "p"
section_ = el "section"
footer_ = el "footer"
button_ = el "button"
input_ = el "input"
select_ = el "select"
ul_ = el "ul"
ol_ = el "ol"
li_ = el "li"
label_ = el "label"
span_ = el "span"
div_ = el "div"
header_ = el "header"
h1_ = el "h1"
h2_ = el "h2"
h3_ = el "h3"
h4_ = el "h4"
h5_ = el "h5"
h6_ = el "h6"
i_ = el "i"
hr_ = el "hr"
img_ = el "img"
strong_ = el "strong"

for_, type_, placeholder_, href_, class_, value_, checked_, autofocus_,
    tabIndex_, src_, name_, disabled_, target_
    :: Attrable a st => a -> Attribute (AttrIntState a st) st algebra parentAlgebra
type_ = attr "type"
placeholder_ = attr "placeholder"
href_ = attr "href"
class_ = attr "class"
for_ = attr "for"
name_ = attr "name"
value_ = attr "value"
checked_ = attr "checked"
autofocus_ = attr "autofocus"
tabIndex_ = attr "tabindex"
src_ = attr "src"
disabled_ = attr "disabled"
target_ = attr "target"

-- Enter exit monad

instance Monad m => Functor (EnterExitT state out m) where
    fmap f a = do x <- a
                  return (f x)
instance Monad m => Applicative (EnterExitT state out m) where
    pure = return
    f <*> x = do f' <- f
                 x' <- x
                 return (f' x')
instance Monad m => Monad (EnterExitT state out m) where
    a >>= b =
        EnterExitT $ \ee out st ->
        do (x, !st') <- runEnterExitT a ee out st
           runEnterExitT (b x) ee out st'
    return x = EnterExitT $ \_ _ st -> return (x, st)
instance MonadIO m => MonadIO (EnterExitT state out m) where
    liftIO f = parentComponent (liftIO f)
instance (RawIO m, Applicative m) => RawIO (EnterExitT state out m) where
    rawIO f = EnterExitT $ \ee out st ->
              fmap (,st) (rawIO f)
instance Monad m => MonadReader out (EnterExitT state out m) where
    local f act =
        EnterExitT $ \ee out st ->
            runEnterExitT act ee (f out) st
    ask = EnterExitT $ \ee out st -> return (out, st)
instance Monad m => MonadState state (EnterExitT state out m) where
    state f =
        EnterExitT $ \ee out st ->
            pure (f st)

instance RawIO IO where
    rawIO = id
instance (RawIO m, Monad m) => RawIO (ReaderT r m) where
    rawIO = lift . rawIO
instance (RawIO m, Monad m) => RawIO (StateT s m) where
    rawIO = lift . rawIO

parentComponent :: MonadIO m => m a -> EnterExitT state out m a
parentComponent action =
    EnterExitT $ \(EnterExit saveState fetchState) out !st ->
    do saveState st
       x <- action
       st' <- fetchState
       return (x, st')
