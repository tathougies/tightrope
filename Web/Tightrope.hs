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
import Control.Monad.Writer
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
import GHCJS.DOM.Element hiding (drop)
import GHCJS.DOM.Node
import GHCJS.DOM.Text
import GHCJS.DOM.Document hiding (drop, evaluate)
import GHCJS.DOM.Types
import GHCJS.DOM.EventTarget
import GHCJS.DOM.HTMLInputElement
import GHCJS.DOM.EventTargetClosures
import GHCJS.DOM.EventM
import GHCJS.DOM.Event
import GHCJS.DOM.NodeList (getLength, item)
import GHCJS.DOM.Window hiding (drop, getLength)
import GHCJS.DOM.RequestAnimationFrameCallback
import qualified GHCJS.DOM.DOMTokenList as TokenList
import GHCJS.DOM.CSSStyleDeclaration hiding (getLength, item)
import GHCJS.Foreign.Callback
import GHCJS.Types

import System.Mem.StableName

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

-- type SnippetConstructor intSt out = DOMInsertPos -> ConstructedSnippet out intSt
-- type SnippetUpdater intSt out = DOMInsertPos -> internalSt -> ConstructedSnippet out intSt
-- data ConstructedSnippet out intSt
--     = ConstructedSnippet
--     { constructedSnippetOut  :: Endo out
--     , constructedAfterAction :: AfterAction out
--     , constructedChildPos    :: DOMInsertPos
--     , constructedSiblingPos  :: DOMInsertPos
--     , constructedState       :: intSt }
--
type SnippetConstructor internalSt out = StateT DOMInsertPos (WriterT (Endo out, AfterAction out) IO) (DOMInsertPos, internalSt)
type SnippetUpdater internalSt out = StateT (DOMInsertPos, internalSt) (WriterT (Endo out, AfterAction out) IO) DOMInsertPos

data a :++ b = !a :++ !b

data Snippet internalSt out state algebra (parentAlgebra :: * -> *)
    = Snippet
    { snippetCreateUnder :: RunAlgebra algebra -> state -> SnippetConstructor internalSt out
    , snippetUpdateElem  :: state -> SnippetUpdater internalSt out
    , snippetFinish      :: ReaderT internalSt IO () }

data Attribute attrSt state algebra (parentAlgebra :: * -> *)
    = Attribute
    { attributeSet    :: RunAlgebra algebra -> state -> Node -> IO attrSt
    , attributeUpdate :: state -> Node -> StateT (DOMInsertPos, attrSt) IO ()
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
                        { mountedStateV   :: MVar (state, internalState)
                        , mountedOutV     :: MVar out
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
runAfterAction (AfterAction []) out = pure ()
runAfterAction (AfterAction (x:xs)) out = x out >> runAfterAction (AfterAction xs) out

foreign import javascript unsafe "console.log($1, $2, $3);" js_log :: Node -> Node -> Node -> IO ()
foreign import javascript unsafe "console.log($1, $2);" js_log2 :: Node -> Node -> IO ()
foreign import javascript unsafe "console.log($1);" js_log1 :: Node -> IO ()
foreign import javascript unsafe "console.log($1);" js_logEvent :: Event -> IO ()
loginsertpos (DOMInsertPos parent Nothing) = js_log1 parent
loginsertpos (DOMInsertPos parent (Just node)) = js_log2 parent node

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

          update st node =
              do (pos, enabled) <- get
                 let enabled' = dyn st

                 when (enabled' /= enabled) $
                      if enabled'
                      then liftIO (enableClass node)
                      else liftIO (disableClass node)

                 put (pos, enabled')

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
              update _ _ =  pure ()
              finish = pure ()

instance Attrable T.Text st where
    type AttrIntState T.Text st = ()

    attr name val = Attribute set update finish
        where set _ _ n = do n <- castToElement n
                             setAttribute n name val
                             pure ()
              update _ _ =  pure ()
              finish = pure ()

instance Attrable Bool st where
    type AttrIntState Bool st = AttrIntState JSString st

    attr name True = attr name name
    attr name False = Attribute (\_ _ _ -> pure ()) (\_ _ -> pure ()) (pure ())

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
            update st n =
                do let newString = mkString newValue
                       newValue = mkValue st
                   (pos, curValue) <- get
                   when (curValue /= newValue) $
                        case newString of
                          Just newString ->
                              doSet n name newString
                          Nothing ->
                              doRemove n name
                   put (pos, newValue)
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

    style_ name val = Attribute set (\_ _ -> pure ()) (pure ())
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

              update st n =
                  do let newValueJS = mkString newValue
                         newValue = mkValue st
                     (pos, curValue) <- get
                     n <- liftIO (castToElement n)
                     Just style <- liftIO (getStyle n)
                     when (curValue /= newValue) $
                          case newValueJS of
                            Just newValueJS ->
                                liftIO (setProperty style name (Just newValueJS) ("" :: JSString))
                            Nothing ->
                                liftIO (void (removeProperty style name :: IO (Maybe JSString)))
                     put (pos, newValue)
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

    update st _ = do (_, (_, stRef)) <- get
                     liftIO (writeIORef stRef st)
                     pure ()

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

      update st _ = do (_, (_, stRef)) <- get
                       liftIO (writeIORef stRef st)
                       pure mempty

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
          set' update _ =
              do tell (Endo (set (RunAlgebraWrapper update)), mempty)
                 pos <- get
                 pure (pos, RunAlgebraWrapper update)

          update _ =
              do (pos, updater) <- get
                 tell (Endo (set updater), mempty)
                 pure pos

onCreate :: forall state algebra out parentAlgebra.
            (state -> algebra ()) -> Snippet () out state algebra parentAlgebra
onCreate action = Snippet create' update' (pure ())
    where create' run st =
              do pos <- get
                 tell (mempty, AfterAction [ \(_ :: out) -> run (action st) ])
                 pure (pos, ())
          update' _ =
              do (pos, _) <- get
                 pure pos

afterDraw :: forall state out algebra parentAlgebra.
             (RunAlgebra algebra -> state -> out -> IO ())
          -> Snippet (RunAlgebraWrapper algebra) out state algebra parentAlgebra
afterDraw action =
    Snippet create' update' (pure ())
  where
    create' :: RunAlgebra algebra -> state -> SnippetConstructor (RunAlgebraWrapper algebra) out
    create' run st =
        do pos <- get
           tell (mempty, AfterAction [ \out -> action run st out ])
           pure (pos, RunAlgebraWrapper run)
    update' st =
        do (pos, RunAlgebraWrapper run) <- get
           tell (mempty, AfterAction [ \out -> action run st out ])
           pure pos

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

    update st _ = do (_, (_, stRef)) <- get
                     liftIO (writeIORef stRef st)

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

    update st _ = do (_, (_, stRef)) <- get
                     liftIO (writeIORef stRef st)
                     pure mempty
    finish = do (release, _) <- ask
                liftIO release

raw_ :: (st -> JSString) -> Snippet Node out st algebra parentAlgebra
raw_ mkHtml = Snippet createUnder updateElem finish
    where
      createUnder _ st =
          do el <- liftIO (mkEl (mkHtml st))

             insertPos <- get
             insertPos' <- liftIO (insertAtPos insertPos (toNode el))
             put insertPos'

             pure (DOMInsertPos (toNode el) Nothing, el)

      updateElem st =
          do (insertPos, el) <- get

             liftIO (finish' el)

             el' <- liftIO (mkEl (mkHtml st))
             insertPos' <- liftIO (insertAtPos insertPos (toNode el'))
             put (insertPos', el')

             pure (DOMInsertPos (toNode el') Nothing)

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
    createUnder _ _ =
      do Just document <- liftIO currentDocument

         Just el <- createElement document (Just tagName)

         insertPos <- get
         insertPos' <- liftIO (insertAtPos insertPos (toNode el))
         put insertPos'

         pure (DOMInsertPos (toNode el) Nothing, el)

    updateElem _ =
      do (_, el) <- get
         modify $ \(DOMInsertPos parent _, st) -> (DOMInsertPos parent (Just (toNode el)), st)
         pure (DOMInsertPos (toNode el) Nothing)

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
    createUnder _ _ =
      do Just document <- liftIO currentDocument

         Just el <- createTextNode document str

         insertPos <- get
         insertPos' <- liftIO (insertAtPos insertPos (toNode el))
         put insertPos'

         pure (DOMInsertPos (toNode el) Nothing, toNode el)

    updateElem _ =
      do (_, el) <- get
         modify $ \(DOMInsertPos parent _, st) -> (DOMInsertPos parent (Just (toNode el)), st)
         pure (DOMInsertPos (toNode el) Nothing)

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

dyn' :: Eq s => (s -> JSString) -> (state -> s) -> Snippet (Text, s) out state algebra parentAlgebra
dyn' toString fromState = Snippet createUnder updateElem finish
  where
    createUnder _ st =
        do Just document <- liftIO currentDocument

           let str = toString strInt
               strInt = fromState st
           Just el <- createTextNode document str

           insertPos <- get
           insertPos' <- liftIO (insertAtPos insertPos (toNode el))
           put insertPos'

           pure (DOMInsertPos (toNode el) Nothing, (el, strInt))

    updateElem st =
        do (_, (txt, str)) <- get

           let str' = toString stInt
               stInt = fromState st
           modify $ \(DOMInsertPos parent _, st) -> (DOMInsertPos parent (Just (toNode txt)), st)
           when (str /= stInt) $
              do setNodeValue txt (Just str')
                 modify $ \(pos, (txt, _)) -> (pos, (txt, stInt))
           pure (DOMInsertPos (toNode txt) Nothing)

    finish =
        do (txt, _) <- ask
           Just parent <- getParentNode txt
           removeChild parent (Just txt)
           pure ()

project_ :: (st -> st')
         -> Snippet intSt out st' algebra parentAlgebra
         -> Snippet intSt out st algebra parentAlgebra
project_ f (Snippet createElem updateElem finishElem) =
    Snippet (\run st -> createElem run (f st))
            (updateElem . f)
            finishElem

enum_ :: forall state ix intSt algebra parentAlgebra out.
         (Enum ix, Ord ix) =>
         (state -> (ix, ix))
      -> Snippet intSt out (Embedded ix state ix) algebra parentAlgebra
      -> Snippet (RunAlgebraWrapper algebra, ix, ix, [intSt]) out state algebra parentAlgebra
enum_ mkBounds (Snippet createItem updateItem finishItem) =
    Snippet createItems updateItems finishItems
  where
    createItems :: RunAlgebra algebra -> state -> SnippetConstructor (RunAlgebraWrapper algebra, ix, ix, [intSt]) out
    createItems runAlgebra state =
        do let (start, end) = mkBounds state

           intSt <- forM [start..end] $ \i ->
                    snd <$> createItem runAlgebra (Embedded state i i)

           pos <- get
           liftIO (putStrLn "Done creating")
           pure (pos, (RunAlgebraWrapper runAlgebra, start, end, intSt))

    updateItems :: state -> SnippetUpdater (RunAlgebraWrapper algebra, ix, ix, [intSt]) out
    updateItems state =
        do (_, (runAlgebra@(RunAlgebraWrapper runAlgebra_), oldStart, oldEnd, intSts)) <- get

           let (newStart, newEnd) = mkBounds state

               newStartIdx = fromEnum newStart
               newEndIdx   = fromEnum newEnd

               oldStartIdx = fromEnum oldStart
               oldEndIdx   = fromEnum oldEnd

               ( (removeFromBeginning, addToBeginning),
                 (removeFromEnd,       addToEnd) )
                 | newEndIdx < newStartIdx =
                     ( (length intSts, []), (0, []) )
                 | newEndIdx < oldStartIdx = -- scrolled up all the way
                     ( (length intSts, [newStart..newEnd]), (0, []) )
                 | newStartIdx > oldEndIdx = -- scrolled down all the way
                     ( (length intSts, [newStart..newEnd]), (0, []) )
                 | otherwise =
                     let beginning | newStartIdx < oldStartIdx = ( 0, [newStart..pred oldStart] )
                                   | otherwise = ( newStartIdx - oldStartIdx, [] )
                         end       | newEndIdx > oldEndIdx = ( 0, [succ oldEnd..newEnd] )
                                   | otherwise = ( oldEndIdx - newEndIdx, [] )
                     in (beginning, end)

               intStsLength = length intSts
               (intSts', removedFromEnd) = splitAt (intStsLength - removeFromEnd) intSts
               (removedFromBeginning, preservedSts) = splitAt removeFromBeginning intSts'

               preservedCount = intStsLength - removeFromBeginning - removeFromEnd
               preservedStart = toEnum (oldStartIdx + removeFromBeginning)

           forM_ (removedFromBeginning <> removedFromEnd) $ \st ->
               liftIO (runReaderT finishItem st)

           addedAtBeginningSts <- forM addToBeginning $ \i ->
                                  do (insertPos, intSt) <- get
                                     ((_, itemIntSt), insertPos') <- lift (runStateT (createItem runAlgebra_ (Embedded state i i)) insertPos)
                                     put (insertPos', intSt)
                                     pure itemIntSt

           updatedSts <- forM (zip [preservedStart..] preservedSts) $ \(i, itemIntSt) ->
                         do (insertPos, intSt) <- get
                            (_, (insertPos', itemIntSt')) <- lift (runStateT (updateItem (Embedded state i i)) (insertPos, itemIntSt))
                            put (insertPos', intSt)
                            pure itemIntSt'

           addedAtEndSts <- forM addToEnd $ \i ->
                            do (insertPos, intSt) <- get
                               ((_, itemIntSt), insertPos') <- lift (runStateT (createItem runAlgebra_ (Embedded state i i)) insertPos)
                               put (insertPos', intSt)
                               pure itemIntSt

           (pos, _) <- get
           put (pos, (runAlgebra, newStart, newEnd, addedAtBeginningSts <> updatedSts <> addedAtEndSts))

           pure pos

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
    createItems runAlgebra state =
        do let current = mkCurrent state

           intSt <- forM (zip [0..] current) $ \(i, item) ->
                    snd <$> createItem runAlgebra (Embedded state item i)

           pos <- get

           pure (pos, (RunAlgebraWrapper runAlgebra, intSt))

    updateItems :: state -> SnippetUpdater (RunAlgebraWrapper algebra, [intSt]) out
    updateItems state =
        do (_, (runAlgebra@(RunAlgebraWrapper runAlgebra_), intSt)) <- get

           let current  = mkCurrent state
               (intSt', toRemove) = splitAt (length current) intSt
               toAdd = drop (length intSt') current

           updatedIntSts <-
               forM (zip3 [0..] current intSt') $ \(i, itemSt, itemIntSt) ->
               do (insertPos, intSt) <- get
                  (_, (insertPos', itemIntSt')) <- lift (runStateT (updateItem (Embedded state itemSt i)) (insertPos, itemIntSt))
                  put (insertPos', intSt)
                  pure itemIntSt'

           forM_ toRemove $ \intSt ->
               liftIO (runReaderT finishItem intSt)

           addedIntSts <- forM (zip [length intSt'..] toAdd) $ \(i, itemSt) ->
               do (insertPos, intSt) <- get
                  ((_, itemIntSt), insertPos') <- lift (runStateT (createItem runAlgebra_ (Embedded state itemSt i)) insertPos)
                  put (insertPos', intSt)
                  pure itemIntSt

           let newIntSts = updatedIntSts ++ addedIntSts
           (pos, _) <- get
           put (pos, (runAlgebra, newIntSts))
           pure pos

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

      update' st node =
          do (pos, (oldKey, x)) <- get
             let newKey = mkKey st
             if oldKey /= newKey
                then do
                  ((), (pos', x')) <- lift (runStateT (update newKey node) (pos, x))
                  put (pos', (newKey, x'))
                else pure ()

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
    createUnder' update st =
        do siblingPos <- get

           (((pos, internalSt), siblingPos'), (mkOut, scheduled)) <-
               lift (lift (runWriterT (runStateT (createUnder update st) siblingPos)))

           put siblingPos'
           tell (mkOut, scheduled)

           pure (pos, (mkKey st, pos, siblingPos', mkOut, internalSt))

    updateElem' st =
        do (siblingPos, oldSt@(oldKey, oldPos, oldSiblingPos, oldMkOut, oldInternalSt)) <- get

           let newKey = mkKey st
           if oldKey == newKey
              then do put (oldSiblingPos, oldSt)
                      tell (oldMkOut, mempty)
                      pure oldPos
              else do ((pos, (siblingPos', internalSt')), (mkOut, scheduled)) <- lift (lift (runWriterT (runStateT (updateElem st) (siblingPos, oldInternalSt))))

                      put (siblingPos', (newKey, pos, siblingPos', mkOut, internalSt'))
                      tell (mkOut, scheduled)

                      pure pos

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
        createUnder' update st =
            do let initialKey = mkKey st
               case mkComponent st initialKey of
                 SomeSnippet (Snippet createUnder updateElem finish) ->
                     do (pos, intSt) <- createUnder update st

                        let intSt' = RenderedSnippet intSt updateElem finish

                        pure (pos, (initialKey, intSt', RunAlgebraWrapper update))

        updateElem' st =
            do let !key = mkKey st
               (siblingPos, (oldKey, rendered, RunAlgebraWrapper update)) <- get
               case rendered of
                 RenderedSnippet intSt updateElem finish ->
                     if key == oldKey
                     then do (childPos, (siblingPos', intSt')) <- lift (runStateT (updateElem st) (siblingPos, intSt))
                             put (siblingPos', (key, RenderedSnippet intSt' updateElem finish, RunAlgebraWrapper update))
                             pure childPos
                     else do lift (lift (runReaderT finish intSt))
                             case mkComponent st key of
                               SomeSnippet (Snippet createUnder updateElem finish) ->
                                   do ((childPos, intSt), siblingPos') <- lift (runStateT (createUnder update st) siblingPos)
                                      put (siblingPos', (key, RenderedSnippet intSt updateElem finish, RunAlgebraWrapper update))
                                      pure childPos

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
        createUnder' update st =
            case check st of
              Just st' ->
                  do (pos, intSt) <- createUnder update (Embedded st st' ())
                     pure (pos, (Just intSt, RunAlgebraWrapper update))
              Nothing -> do pos <- get
                            pure (pos, (Nothing, RunAlgebraWrapper update))

        updateElem' st =
            do (pos, (intSt, RunAlgebraWrapper update)) <- get
               case (check st, intSt) of
                 (Nothing, Nothing) -> pure pos
                 (Just st', Nothing) ->
                     do ((childPos, intSt'), siblingPos) <- lift (runStateT (createUnder update (Embedded st st' ())) pos)
                        put (siblingPos, (Just intSt', RunAlgebraWrapper update))

                        pure childPos
                 (Nothing, Just childSt) ->
                     do liftIO (runReaderT finish childSt)
                        put (pos, (Nothing, RunAlgebraWrapper update))
                        pure pos
                 (Just st', Just childSt) ->
                     do (childPos, (siblingPos, intSt')) <- lift (runStateT (updateElem (Embedded st st' ())) (pos, childSt))
                        pure (siblingPos, (Just intSt', RunAlgebraWrapper update))
                        pure childPos

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
        (:++) <$> setLeft runAlgebra st node
              <*> setRight runAlgebra st node

    update st node =
        do (pos, (left :++ right)) <- get
           ((), (pos', left')) <- lift (runStateT (updateLeft st node) (pos, left))
           ((), (pos'', right')) <- lift (runStateT (updateRight st node) (pos', right))
           put (pos'', (left' :++ right'))

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
        createUnder runAlgebra st =
            do (left, leftIntSt) <- createLeft runAlgebra st
               (right, rightIntSt) <- createRight runAlgebra st

               pure (right, (leftIntSt :++ rightIntSt))

        updateElem st =
            do (siblingInsertPos, (leftIntSt :++ rightIntSt)) <- get

               (left, (siblingInsertPos', leftIntSt')) <- lift (runStateT (updateLeft st) (siblingInsertPos, leftIntSt))
               (right, (siblingInsertPos'', rightIntSt')) <- lift (runStateT (updateRight st) (siblingInsertPos', rightIntSt))

               put (siblingInsertPos'', (leftIntSt' :++ rightIntSt'))

               pure left

        finish =
            do (leftSt :++ rightSt) <- ask
               lift (runReaderT finishLeft leftSt)
               lift (runReaderT finishRight rightSt)

-- {-# INLINE (|-*) #-}
(|-*) :: Snippet parentEl out state algebra parentAlgebra
      -> SomeSnippet out state algebra parentAlgebra
      -> Snippet (parentEl :++ RenderedSnippet out state) out state algebra parentAlgebra
parent |-* child = parent |- someSnippet_ child

-- {-# INLINE (|-) #-}
(|-) :: forall parentEl childEl state algebra parentAlgebra out.
        Snippet parentEl out state algebra parentAlgebra
     -> Snippet childEl out state algebra parentAlgebra
     -> Snippet (parentEl :++ childEl) out state algebra parentAlgebra
Snippet createParent updateParent finishParent |- Snippet createChild updateChild finishChild =
  Snippet createUnder' updateElem' finish'
  where createUnder' :: RunAlgebra algebra -> state -> SnippetConstructor (parentEl :++ childEl) out
        createUnder' runAlgebra st =
          do (parent@(DOMInsertPos parentNode _), !parentIntSt) <- createParent runAlgebra st
             ((_, !childIntSt), parent') <- lift (runStateT (createChild runAlgebra st) parent)

             return (parent', (parentIntSt :++ childIntSt))

        updateElem' st =
          do (siblingInsertPos, (parentIntSt :++ childIntSt)) <- get

             (parentInsertPos@(DOMInsertPos parentNode _), (!siblingInsertPos', !parentIntSt')) <- lift (runStateT (updateParent st) (siblingInsertPos, parentIntSt))
             (_, (parentInsertPos', !childIntSt')) <- lift (runStateT (updateChild st) (parentInsertPos, childIntSt))

             put (siblingInsertPos', (parentIntSt' :++ childIntSt'))

             pure parentInsertPos'

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
        createUnder' runAlgebra st =
          do insertPos <- get

             (el, !elIntSt) <- createUnder runAlgebra st
             !attrSt <- liftIO (setAttr runAlgebra st (insertPosParent el))

             pure (el, (elIntSt :++ attrSt))

        updateElem' st =
          do (insertPos, (elSt :++ attrSt)) <- get

             (parentInsertPos, (insertPos', !elSt')) <- lift (runStateT (updateElem st) (insertPos, elSt))
             ((), (insertPos'', !attrSt')) <- liftIO (runStateT (updateAttr st (insertPosParent parentInsertPos)) (insertPos', attrSt))

             put (insertPos'', (elSt' :++ attrSt'))

             pure parentInsertPos

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
          createUnder' run st =
              do res@(_, st') <- createUnder run st
                 tell (Endo (modOut st'), mempty)
                 pure res
          updateElem' st =
              do res <- updateElem st
                 (_, st) <- get
                 tell (Endo (modOut st), mempty)
                 pure res

someSnippet_ :: forall out state algebra parentAlgebra.
                SomeSnippet out state algebra parentAlgebra
             -> Snippet (RenderedSnippet out state) out state algebra parentAlgebra
someSnippet_ (SomeSnippet (Snippet createUnder updateElem finish)) =
    Snippet createUnder' updateElem' finish'
  where
    createUnder' :: RunAlgebra algebra -> state -> SnippetConstructor (RenderedSnippet out state) out
    createUnder' update st =
        do (pos, intSt) <- createUnder update st
           let snippet' = RenderedSnippet intSt updateElem finish
           pure (pos, snippet')

    updateElem' st =
        do (siblingPos, RenderedSnippet intSt updateElem finish) <- get
           (parentPos, (siblingPos', intSt')) <- lift (runStateT (updateElem st) (siblingPos, intSt))
           put (siblingPos', RenderedSnippet intSt' updateElem finish)
           pure parentPos

    finish' :: ReaderT (RenderedSnippet out state) IO ()
    finish' = do RenderedSnippet intSt _ finish <- ask
                 lift (runReaderT finish intSt)

mount_ :: forall childAlgebra out st algebra parentAlgebra.
          MonadIO algebra =>
          (st -> EmbeddedAlgebraWrapper childAlgebra algebra -> out -> out) -> (st -> Component childAlgebra algebra)
       -> Snippet (MountedComponent childAlgebra algebra) out st algebra parentAlgebra
mount_ setChild mkComponent = Snippet createUnder updateElem finish
    where createUnder :: RunAlgebra algebra -> st -> SnippetConstructor (MountedComponent childAlgebra algebra) out
          createUnder update st =
            case mkComponent st of
              Component { componentTemplate = componentTemplate@(Snippet { .. })
                        , .. } -> do
                 stVar  <- liftIO newEmptyMVar
                 outVar <- liftIO newEmptyMVar
                 doneVar <- liftIO (newMVar False)
                 siblingVar <- liftIO newEmptyMVar

                 redrawStateVar <- liftIO (newMVar Nothing)
                 Just window <- liftIO currentWindow

                 let redraw _ = do scheduled <- bracket (takeMVar doneVar) (putMVar doneVar) $ \isDone ->
                                                if not isDone then
                                                    do modifyMVar_ redrawStateVar $ \_ -> pure Nothing

                                                       (st, intSt) <- takeMVar stVar
                                                       (insPos, _, childPos) <- takeMVar siblingVar
                                                       ((childPos, (insPos', !intSt')), (Endo mkOut, scheduled)) <-
                                                           runWriterT (runStateT (snippetUpdateElem st) (insPos, intSt))

                                                       putMVar stVar (st, intSt')
                                                       putMVar siblingVar (insPos, insPos', childPos)
                                                       modifyMVar_ outVar $ \_ -> pure (mkOut componentEmptyOut)
                                                       out' <- readMVar outVar
                                                       pure (runAfterAction scheduled out')
                                                  else pure (pure ())
                                   scheduled

                 redrawCallback <- newRequestAnimationFrameCallback redraw

                 let intSt = MountedComponent stVar outVar siblingVar
                                              componentEmptyOut (EmbeddedAlgebraWrapper runAlgebra'') finish
                                              componentRunAlgebra componentTemplate

                     finish = do isDone <- takeMVar doneVar
                                 putMVar doneVar True

                                 when (not isDone) $
                                   do redrawState <- readMVar redrawStateVar
                                      case redrawState of
                                        Nothing -> pure ()
                                        Just id -> cancelAnimationFrame window id

                                      let RequestAnimationFrameCallback cb = redrawCallback
                                      releaseCallback cb

                                      (st, intSt) <- readMVar stVar
                                      runReaderT snippetFinish intSt

                     runAlgebra'' :: forall a. childAlgebra a -> algebra a
                     runAlgebra'' a = do (st, intSt) <- liftIO (takeMVar stVar)
                                         out <- liftIO (readMVar outVar)
                                         isDone <- liftIO (readMVar doneVar)
                                         oldStNm <- liftIO (makeStableName st)
                                         (x, !st') <- componentRunAlgebra (EnterExit (\(!st) -> liftIO (putMVar stVar (st, intSt))) (liftIO (fst <$> takeMVar stVar))) st out a
                                         newStNm <- liftIO (makeStableName st')

                                         liftIO $ if isDone then putMVar stVar (st, intSt) else putMVar stVar (st', intSt)

                                         when (oldStNm /= newStNm && not isDone)
                                              (liftIO . modifyMVar_ redrawStateVar $ \redrawState ->
                                                   case redrawState of
                                                     Nothing ->
                                                         do id <- requestAnimationFrame window (Just redrawCallback)
                                                            pure (Just id)
                                                     Just id -> pure (Just id))

                                         pure x

                     runAlgebra' :: forall a. childAlgebra a -> IO a
                     runAlgebra' = update . runAlgebra''

                 siblingPos <- get

                 (((childPos, compIntSt), siblingPos'), (Endo mkOut, scheduled)) <-
                     lift (lift (runWriterT (runStateT (snippetCreateUnder runAlgebra' componentStateInitial) siblingPos)))
                 put siblingPos'

                 out' <- liftIO $ do
                   putMVar stVar (componentStateInitial, compIntSt)
                   putMVar outVar (mkOut componentEmptyOut)
                   putMVar siblingVar (siblingPos, siblingPos', childPos)
                   readMVar outVar

                 tell ( Endo (setChild st (EmbeddedAlgebraWrapper runAlgebra''))
                      , AfterAction [ \_ -> runAlgebra' (componentOnConstruct runAlgebra')
                                    , \_ -> runAfterAction scheduled out' ] )

                 pure (childPos, intSt)

          updateElem st =
              do (insPos, mc@MountedComponent { .. }) <- get
                 (_, insPos', childPos) <- liftIO (readMVar mountedInsPosV)
                 put (insPos', mc)

                 tell (Endo (setChild st mountedAlgebraWrapper), mempty)

                 pure childPos

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
emptySnippet = Snippet (\_ _ -> (, ()) <$> get) (\_ -> fst <$> get) (return ())

mountComponent :: Element -> Component algebra IO -> IO ()
mountComponent el (Component st emptyOut runAlgebra onCreate (Snippet createTemplate updateTemplate finishTemplate :: Snippet intSt st out algebra IO))  =
  do stVar <- newEmptyMVar
     outVar <- newEmptyMVar
     syncVar <- newMVar ()

     Just window <- currentWindow

     redrawStateVar <- newMVar Nothing
     let redraw _ = do modifyMVar_ redrawStateVar $ \_ -> pure Nothing
                       (st, intSt) <- takeMVar stVar
                       ((_, (_, intSt')), (Endo mkOut, scheduled)) <- runWriterT (runStateT (updateTemplate st) (DOMInsertPos (toNode el) Nothing, intSt))
                       putMVar stVar (st, intSt')
                       modifyMVar_ outVar $ \_ -> pure (mkOut emptyOut)
                       out' <- readMVar outVar
                       runAfterAction scheduled out'

     redrawCallback <- newRequestAnimationFrameCallback redraw

     let runAlgebra' :: forall a. algebra a -> IO a
         runAlgebra' a = bracket (takeMVar syncVar) (putMVar syncVar) $ \_ ->
                         do (x, shouldRedraw) <- modifyMVar stVar $ \(st, intSt) ->
                                 do out <- readMVar outVar
                                    oldStNm <- makeStableName st
                                    (x, !st') <- runAlgebra (EnterExit (\st -> putMVar stVar (st, intSt)) (fst <$> takeMVar stVar)) st out a
                                    newStNm <- makeStableName st'
                                    pure ((st', intSt), (x, oldStNm /= newStNm))

                            when shouldRedraw scheduleRedraw

                            pure x
         scheduleRedraw = do
           redrawState <- takeMVar redrawStateVar
           case redrawState of
             Nothing ->
                 do id <- requestAnimationFrame window (Just redrawCallback)
                    putMVar redrawStateVar (Just id)
             Just _ -> putMVar redrawStateVar redrawState

     (((_, intSt), _), (Endo mkOut, scheduled)) <- runWriterT (runStateT (createTemplate runAlgebra' st) (DOMInsertPos (toNode el) Nothing))

     putMVar stVar (st, intSt)
     putMVar outVar (mkOut emptyOut)

     runAlgebra' (onCreate runAlgebra')
     out' <- readMVar outVar
     runAfterAction scheduled out'

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
instance Monad m => MonadReader out (EnterExitT state out m) where
    local f act =
        EnterExitT $ \ee out st ->
            runEnterExitT act ee (f out) st
    ask = EnterExitT $ \ee out st -> return (out, st)
instance Monad m => MonadState state (EnterExitT state out m) where
    state f =
        EnterExitT $ \ee out st ->
            pure (f st)

parentComponent :: MonadIO m => m a -> EnterExitT state out m a
parentComponent action =
    EnterExitT $ \(EnterExit saveState fetchState) out !st ->
    do saveState st
       x <- action
       st' <- fetchState
       return (x, st')
