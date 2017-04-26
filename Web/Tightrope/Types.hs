{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}

module Web.Tightrope.Types where

import Control.Concurrent.MVar
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative
import Control.Lens

import qualified Data.Text as T
import Data.Monoid
import Data.IORef
import Data.Proxy
import Data.String
import Data.Typeable
#ifdef __GHCJS__
import Data.JSString (JSString)
import Data.JSString.Text (textToJSString, textFromJSString)
#endif

import System.Mem.StableName

class IsText t where
    fromText :: T.Text -> t
    toText :: t -> T.Text
instance IsText T.Text where
    fromText = id
    toText = id

#ifdef __GHCJS__
instance IsText JSString where
    fromText = textToJSString
    toText = textFromJSString

class IsJSS t where
    fromJSS :: JSString -> t
    toJSS :: t -> JSString
instance IsJSS T.Text where
    fromJSS = textFromJSString
    toJSS   = textToJSString
instance IsJSS JSString where
    fromJSS = id
    toJSS = id
#endif

class RawIO m where
    rawIO :: IO a -> m a

class ( Monoid (Text impl), Eq (Text impl)
      , IsString (Text impl), IsText (Text impl)
#ifdef __GHCJS__
      , IsJSS (Text impl)
#endif
      , Typeable impl) => TightropeImpl impl where
    type Node impl  :: *
    type Text impl  :: *
    data Event impl :: * -> *

    createElement  :: Proxy impl -> Text impl -> IO (Node impl)
    createTextNode :: Proxy impl -> Text impl -> IO (Node impl)

    addEventListener :: Node impl -> Event impl e -> ReaderT e IO () -> IO (IO ())
    addBodyEventListener :: Event impl e -> ReaderT e IO () -> IO (IO ())
    addResizeListener :: Proxy impl -> ((Double, Double) -> IO ()) -> IO (IO ())

    insertAtPos    :: Proxy impl -> DOMInsertPos impl -> Node impl -> IO (DOMInsertPos impl)
    removeChild    :: Proxy impl -> Node impl -> IO ()

    addClasses :: Proxy impl -> Node impl -> Text impl -> IO ()
    enableClass    :: Proxy impl -> Node impl -> Text impl -> IO ()
    disableClass   :: Proxy impl -> Node impl -> Text impl -> IO ()

    setAttribute   :: Proxy impl -> Node impl -> Text impl -> Maybe (Text impl) -> IO ()
    setStyle       :: Proxy impl -> Node impl -> Text impl -> Maybe (Text impl) -> IO ()
    setNodeValue   :: Proxy impl -> Node impl -> Text impl -> IO ()

    requestFrame   :: Proxy impl -> (Double -> IO ()) -> IO ()

type RunAlgebra algebra = forall a. algebra a -> IO a
type GenericRunAlgebra algebra = forall a m. MonadIO m => algebra a -> m a

data EnterExit state out m m' = EnterExit (state -> IO ()) (IO state) (RunAlgebra m) (RunAlgebra m')

newtype RunAlgebraWrapper algebra = RunAlgebraWrapper (RunAlgebra algebra)
newtype EmbeddedAlgebraWrapper algebra (parentAlgebra :: * -> *) =
    EmbeddedAlgebraWrapper (forall a m. MonadIO m => algebra a -> m a)
newtype EnterExitT state out m a = EnterExitT { runEnterExitT :: EnterExit state out m (EnterExitT state out m) -> out -> state -> IO (a, state) }

data DOMInsertPos impl
    = DOMInsertPos
    { insertPosParent :: Node impl
    , insertPosPrevSibling :: Maybe (Node impl) }

newtype AfterAction out = AfterAction [ out -> IO () ]

newtype Snippet' impl out state algebra = Snippet (RunAlgebra algebra -> state -> IO state -> DOMInsertPos impl -> IO (ConstructedSnippet impl out state algebra))
data ConstructedSnippet impl out state algebra
    = ConstructedSnippet
    { constructedSnippetOut  :: Endo out
    , constructedAfterAction :: AfterAction out
    , constructedSiblingPos  :: DOMInsertPos impl
    , constructedChildPos    :: DOMInsertPos impl
    , constructedSnippetNext :: Snippet' impl out state algebra
    , constructedSnippetFinish :: IO () }

newtype Attribute' impl out st algebra = Attribute (Snippet' impl out st algebra)

type GenericSnippet = forall impl st out algebra. TightropeImpl impl => Snippet' impl st out algebra

data Component' impl props (algebra :: * -> *) (parentAlgebra :: * -> *) where
    Component :: MonadIO parentAlgebra =>
                 { componentInitState     :: props -> state
                 , componentEmptyOut      :: out
                 , componentRunAlgebra    :: forall a. EnterExit state out parentAlgebra algebra -> state -> out -> algebra a -> IO (a, state)
                 , componentOnConstruct   :: RunAlgebra algebra -> props -> algebra ()
                 , componentOnPropsUpdate :: props -> algebra ()
                 , componentTemplate      :: Snippet' impl out state algebra }
              -> Component' impl props algebra parentAlgebra

data MountedComponent impl algebra parentAlgebra where
    MountedComponent :: MonadIO parentAlgebra =>
                        { mountedStateV         :: MVar state
                        , mountedOutV           :: IORef out
                        , mountedInsPosV        :: MVar (DOMInsertPos impl, DOMInsertPos impl, DOMInsertPos impl)
                        , mountedEmptyOut       :: out
                        , mountedAlgebraWrapper :: EmbeddedAlgebraWrapper algebra parentAlgebra
                        , mountedFinish         :: IO ()
                        , mountedRunAlgebra     :: forall a. EnterExit state out parentAlgebra algebra -> state -> out -> algebra a ->  IO (a, state)
                        , mountedTemplate       :: Snippet' impl out state algebra }
                     -> MountedComponent impl algebra parentAlgebra

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

emptySnippet :: Snippet' impl out state algebra
emptySnippet = Snippet $ \_ _ _ pos ->
               pure (ConstructedSnippet mempty mempty pos pos emptySnippet (return ()))

instance Monoid (Snippet' impl out state m) where
    mempty = emptySnippet
    mappend (Snippet left) (Snippet right) =
        Snippet $ \runAlgebra st getSt siblingPos ->
            do ConstructedSnippet leftOut leftScheduled siblingPos' _ left' finishLeft <-
                   left runAlgebra st getSt siblingPos
               ConstructedSnippet rightOut rightScheduled siblingPos'' childPos right' finishRight <-
                   right runAlgebra st getSt siblingPos'
               pure (ConstructedSnippet (leftOut <> rightOut) (leftScheduled <> rightScheduled)
                                        siblingPos'' childPos (mappend left' right') (finishLeft >> finishRight))

-- * EnterExit monad

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
instance Monad m => MonadIO (EnterExitT state out m) where
    liftIO f = EnterExitT $ \(EnterExit saveState fetchState runParent _) out !st ->
               do saveState st
                  x <- f
                  st' <- fetchState
                  return (x, st')
instance RawIO (EnterExitT state out m) where
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

getUpdater :: MonadIO m => EnterExitT state out m (RunAlgebraWrapper (EnterExitT state out m))
getUpdater = EnterExitT $ \(EnterExit _ _ _ update) out st ->
             pure (RunAlgebraWrapper update, st)

parentComponent :: MonadIO m => m a -> EnterExitT state out m a
parentComponent action =
    EnterExitT $ \(EnterExit saveState fetchState runParent _) out !st ->
    do saveState st
       x <- runParent action
       st' <- fetchState
       return (x, st')

-- * Dummy implementation

data DummyImpl

instance TightropeImpl DummyImpl where
    type Node DummyImpl = ()
    type Text DummyImpl = T.Text
    data Event DummyImpl e

    createElement _ _ = pure ()
    createTextNode _ _ = pure ()

    addEventListener _ _ _ = pure (pure ())
    addBodyEventListener _ _ = pure (pure ())
    addResizeListener _ _ = pure (pure ())

    insertAtPos _ _ _ = pure (DOMInsertPos () Nothing)
    removeChild _ _ = pure ()

    addClasses _ _ _ = pure ()
    enableClass _ _ _ = pure ()
    disableClass _ _ _ = pure ()

    setAttribute _ _ _ _ = pure ()
    setStyle _ _ _ _ = pure ()
    setNodeValue _ _ _ = pure ()

    requestFrame _ _ = pure ()

(~~~) :: (MonadState s m, MonadIO m) => Lens' s v -> v -> m ()
lens ~~~ v =
    do oldVal <- use lens
       oldNm <- liftIO (makeStableName oldVal)
       newNm <- liftIO (makeStableName v)
       if oldNm /= newNm
          then modify (lens .~ v)
          else pure ()

(~==~) :: (MonadState s m, MonadIO m, Eq v) => Lens' s v -> v -> m ()
lens ~==~ v =
    do oldVal <- use lens
       if oldVal /= v
          then modify (lens .~ v)
          else pure ()
infixr 4 ~~~, ~==~
