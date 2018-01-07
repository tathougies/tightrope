{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Web.Tightrope.Static
    ( StaticImpl

    , StaticNode(..)
    , IONode, FrozenNode

    , Snippet, Attribute
    , Component, Node

    , TT.TightropeEventImpl(..)

    , renderSnippetStatic
    , mountComponent
    , freezeNode ) where

import Web.Tightrope.Types hiding (Node)
import qualified Web.Tightrope.Types as TT
import qualified Web.Tightrope.Event as TT

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Identity
import Control.Concurrent.MVar
import Control.Exception (bracketOnError)

import qualified Data.HashSet as S
import qualified Data.HashMap.Strict as M
import qualified Data.Text as T
import Data.Monoid
import Data.IORef

data StaticImpl

data StaticNode ref
    = StaticNode
    { nodeFirstChild      :: ref (Maybe (StaticNode ref))
    , nodeParent          :: ref (Maybe (StaticNode ref))
    , nodeNext, nodePrev  :: ref (Maybe (StaticNode ref))

    , nodeTagName         :: ref T.Text
    , nodeClasses         :: ref (S.HashSet T.Text)
    , nodeAttributes      :: ref (M.HashMap T.Text T.Text)
    , nodeStyle           :: ref (M.HashMap T.Text T.Text) }

    | StaticText
    { nodeParent          :: ref (Maybe (StaticNode ref))
    , nodeNext, nodePrev :: ref (Maybe (StaticNode ref))

    , nodeText            :: ref T.Text }

type IONode = StaticNode IORef
type FrozenNode = StaticNode Identity
deriving instance Eq IONode
deriving instance Show FrozenNode

-- * Specializations

type Snippet = Snippet' StaticImpl
type Attribute = Attribute' StaticImpl
type Component = Component' StaticImpl
type Node = TT.Node StaticImpl

-- * Instance for TightropeImpl

instance TightropeImpl StaticImpl where
    type Node StaticImpl = IONode
    type Text StaticImpl = T.Text
    data Event StaticImpl e = StaticEvent

    createElement _ = newNode
    createTextNode _ = newTextNode

    addEventListener _ _ _ = pure (pure ())
    addBodyEventListener _ _ = pure (pure ())
    addResizeListener _ _ = pure (pure ())

    insertAtPos _ (DOMInsertPos parent Nothing) child =
        do extractNode child
           prependChild parent child
           pure (DOMInsertPos parent (Just child))
    insertAtPos _ (DOMInsertPos parent (Just prevSibling)) child =
        do verifyIsParent parent prevSibling
           insertAfter prevSibling child
           pure (DOMInsertPos parent (Just child))

    removeChild _ = extractNode

    addClasses p node classes =
        mapM_ (enableClass p node) (T.words classes)

    enableClass _ node className =
        modifyIORef' (nodeClasses node) (S.insert className)
    disableClass _ node className =
        modifyIORef' (nodeClasses node) (S.delete className)

    setAttribute _ node key value =
        modifyIORef' (nodeAttributes node) $ \attrs ->
        case value of
          Nothing -> M.delete key attrs
          Just value -> M.insert key value attrs
    setStyle _ node key value = do
        tg <- readIORef (nodeTagName node)
        classes <- readIORef (nodeClasses node)

        modifyIORef' (nodeStyle node) $ \styles ->
          case value of
            Nothing -> M.delete key styles
            Just value -> M.insert key value styles

    setNodeValue _ node content =
        writeIORef (nodeText node) content

    requestFrame _ redraw = redraw 0

instance TT.TightropeEventImpl StaticImpl where
    type MouseEventImpl StaticImpl = ()
    type KeyboardEventImpl StaticImpl = ()
    type ClipboardEventImpl StaticImpl = ()
    type EventImpl StaticImpl = ()

    dblClick    = StaticEvent
    click       = StaticEvent

    keyDown     = StaticEvent
    keyUp       = StaticEvent
    keyPress    = StaticEvent

    mouseUp     = StaticEvent
    mouseDown   = StaticEvent
    mouseEnter  = StaticEvent
    mouseLeave  = StaticEvent
    mouseOver   = StaticEvent
    mouseOut    = StaticEvent
    mouseMove   = StaticEvent
    contextMenu = StaticEvent

    drag        = StaticEvent
    drop        = StaticEvent
    dragStart   = StaticEvent
    dragEnd     = StaticEvent
    dragEnter   = StaticEvent
    dragLeave   = StaticEvent
    dragOver    = StaticEvent

    cutEvent    = StaticEvent
    copyEvent   = StaticEvent
    pasteEvent  = StaticEvent

    focusEvent  = StaticEvent
    blurEvent   = StaticEvent
    change      = StaticEvent

-- * Node implementation

newNode, newTextNode :: T.Text -> IO IONode
newNode tagName =
    StaticNode
    <$> newIORef Nothing
    <*> newIORef Nothing
    <*> newIORef Nothing
    <*> newIORef Nothing

    <*> newIORef tagName
    <*> newIORef mempty
    <*> newIORef mempty
    <*> newIORef mempty

newTextNode content =
    StaticText
    <$> newIORef Nothing
    <*> newIORef Nothing
    <*> newIORef Nothing

    <*> newIORef content

verifyIsParent :: IONode -> IONode -> IO Bool
verifyIsParent parent child =
    do parent' <- readIORef (nodeParent child)
       case parent' of
         Nothing -> pure False
         Just parent' ->
             pure (parent == parent')

extractNode :: IONode -> IO ()
extractNode node =
    do parent <- readIORef (nodeParent node)
       case parent of
         Nothing -> pure ()
         Just parent ->
             do parentFirstNode <- readIORef (nodeFirstChild parent)
                when (parentFirstNode == Just node) $ do
                  next <- readIORef (nodeNext node)
                  writeIORef (nodeFirstChild parent) next

                next <- readIORef (nodeNext parent)
                prev <- readIORef (nodePrev parent)

                case (prev, next) of
                  (Nothing, Nothing) -> pure ()
                  (Nothing, Just next) ->
                      writeIORef (nodePrev next) Nothing
                  (Just prev, Nothing) ->
                      writeIORef (nodeNext prev) Nothing
                  (Just prev, Just next) ->
                      writeIORef (nodeNext prev) (Just next) >>
                      writeIORef (nodePrev next) (Just prev)

prependChild :: IONode -> IONode -> IO ()
prependChild parent child =
    do firstChild <- readIORef (nodeFirstChild parent)

       writeIORef (nodeFirstChild parent) (Just child)

       writeIORef (nodePrev child) Nothing
       writeIORef (nodeNext child) firstChild
       case firstChild of
         Nothing -> pure ()
         Just firstChild -> writeIORef (nodePrev firstChild) (Just child)

       writeIORef (nodeParent child) (Just parent)

insertAfter :: IONode -> IONode -> IO ()
insertAfter prev child =
    do next <- readIORef (nodeNext prev)

       writeIORef (nodeNext prev) (Just child)
       writeIORef (nodePrev child) (Just prev)
       writeIORef (nodeNext child) next
       case next of
         Nothing -> pure ()
         Just next -> writeIORef (nodePrev next) (Just child)

       writeIORef (nodeParent child) =<< readIORef (nodeParent prev)

-- * Backend-specific functions

renderSnippetStatic :: props -> Component props algebra IO -> IO FrozenNode
renderSnippetStatic initialProps comp = do
  (_, n) <- mountComponent initialProps comp
  freezeNode n

mountComponent :: forall props algebra. props -> Component props algebra IO -> IO (props -> IO (), Node)
mountComponent initialProps (Component mkSt emptyOut runAlgebra onCreate onPropsUpdate (Snippet constructTemplate)) =
  do stVar <- newEmptyMVar
     intStVar <- newEmptyMVar

     rootNode <- newNode ""

     let runAlgebra' :: forall a. algebra a -> IO a
         runAlgebra' a = do
           (x, scheduled, out) <-
             bracketOnError (takeMVar stVar) (putMVar stVar) $ \st ->
                 bracketOnError (takeMVar intStVar) (putMVar intStVar) $ \(out, Snippet updateTemplate, finishTemplate) -> do
                   (x, st') <- runAlgebra (EnterExit (putMVar stVar) (takeMVar stVar) id runAlgebra') st out a

                   ConstructedSnippet (Endo mkOut) scheduled _ _ updateTemplate' finishTemplate' <-
                     updateTemplate runAlgebra' st getSt (DOMInsertPos rootNode Nothing)

                   let out' = mkOut emptyOut
                   putMVar intStVar (out', updateTemplate', finishTemplate')
                   putMVar stVar st'
                   pure (x, scheduled, out')

           runAfterAction scheduled out
           pure x

         getSt = readMVar stVar
         initialState = mkSt initialProps

     putMVar stVar initialState
     ConstructedSnippet (Endo mkOut) scheduled _ _ snippet' finish <-
         constructTemplate runAlgebra' initialState getSt (DOMInsertPos rootNode Nothing)
     let initialOut = mkOut emptyOut
     putMVar intStVar (initialOut, snippet', finish)

     runAfterAction scheduled initialOut
     runAlgebra' (onCreate runAlgebra' initialProps)

     pure (\newProps -> runAlgebra' (onPropsUpdate newProps), rootNode)

mapNode :: forall m g f.
           Monad m =>
           (f (Maybe (StaticNode f)) -> m (Maybe (StaticNode f)))
        -> (forall a. f a -> m a)
        -> (forall a. a -> m (g a))
        -> StaticNode f
        -> m (StaticNode g)
mapNode readParent read mk (StaticNode firstChild parent next prev tagName classes attributes style) =
    StaticNode <$> (r =<< read firstChild)
               <*> (r =<< readParent parent)
               <*> (r =<< read next)
               <*> (r =<< readParent prev)
               <*> (mk =<< read tagName)
               <*> (mk =<< read classes)
               <*> (mk =<< read attributes)
               <*> (mk =<< read style)
  where
    r :: Maybe (StaticNode f) -> m (g (Maybe (StaticNode g)))
    r Nothing = mk Nothing
    r (Just x) = mk =<< (Just <$> mapNode readParent read mk x)
mapNode readParent read mk (StaticText parent next prev text) =
    StaticText <$> (r =<< readParent  parent)
               <*> (r =<< read next)
               <*> (r =<< readParent prev)
               <*> (mk =<< read text)
  where
    r :: Maybe (StaticNode f) -> m (g (Maybe (StaticNode g)))
    r Nothing = mk Nothing
    r (Just x) = mk =<< (Just <$> mapNode readParent read mk x)

freezeNode :: IONode -> IO FrozenNode
freezeNode = mapNode (const (pure Nothing)) readIORef (pure . Identity)
