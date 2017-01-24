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

type SnippetConstructor impl intSt out = DOMInsertPos impl -> IO (ConstructedSnippet impl intSt out)
type SnippetUpdater impl intSt out = DOMInsertPos impl -> intSt -> IO (ConstructedSnippet impl intSt out)
data ConstructedSnippet impl intSt out
    = ConstructedSnippet
    { constructedSnippetOut  :: Endo out
    , constructedAfterAction :: AfterAction out
    , constructedSiblingPos  :: DOMInsertPos impl
    , constructedChildPos    :: DOMInsertPos impl
    , constructedState       :: intSt }

-- type SnippetConstructor internalSt out = StateT DOMInsertPos (WriterT (Endo out, AfterAction out) IO) (DOMInsertPos, internalSt)
-- type SnippetUpdater internalSt out = StateT (DOMInsertPos, internalSt) (WriterT (Endo out, AfterAction out) IO) DOMInsertPos

data a :++ b = !a :++ !b

data Snippet' impl internalSt out state algebra (parentAlgebra :: * -> *)
    = Snippet
    { snippetCreateUnder :: RunAlgebra algebra -> state -> IO state -> SnippetConstructor impl internalSt out
    , snippetUpdateElem  :: RunAlgebra algebra -> state -> IO state ->  SnippetUpdater impl internalSt out
    , snippetFinish      :: internalSt -> IO () }

type GenericSnippet = forall impl st out algebra parentAlgebra. TightropeImpl impl => Snippet' impl (Node impl) st out algebra parentAlgebra

data Attribute' impl attrSt state algebra (parentAlgebra :: * -> *)
    = Attribute
    { attributeSet    :: RunAlgebra algebra -> state -> IO state -> Node impl -> IO attrSt
    , attributeUpdate :: RunAlgebra algebra -> state -> Node impl -> attrSt -> IO attrSt
    , attributeFinish :: attrSt -> IO () }

data Component' impl props (algebra :: * -> *) (parentAlgebra :: * -> *) where
    Component :: MonadIO parentAlgebra =>
                 { componentStateInitial :: state
                 , componentEmptyOut     :: out
                 , componentRunAlgebra   :: forall a. EnterExit state out parentAlgebra algebra -> state -> out -> algebra a -> IO (a, state)
                 , componentOnConstruct  :: RunAlgebra algebra -> algebra ()
                 , componentOnPropsUpdate :: props -> algebra ()
                 , componentTemplate     :: Snippet' impl internalSt out state algebra parentAlgebra }
              -> Component' impl props algebra parentAlgebra

data MountedComponent impl algebra parentAlgebra where
    MountedComponent :: MonadIO parentAlgebra =>
                        { mountedStateV         :: MVar state
                        , mountedIntStateV      :: IORef internalSt
                        , mountedOutV           :: IORef out
                        , mountedInsPosV        :: MVar (DOMInsertPos impl, DOMInsertPos impl, DOMInsertPos impl)
                        , mountedEmptyOut       :: out
                        , mountedAlgebraWrapper :: EmbeddedAlgebraWrapper algebra parentAlgebra
                        , mountedFinish         :: IO ()
                        , mountedRunAlgebra     :: forall a. EnterExit state out parentAlgebra algebra -> state -> out -> algebra a ->  IO (a, state)
                        , mountedTemplate       :: Snippet' impl internalSt out state algebra parentAlgebra }
                     -> MountedComponent impl algebra parentAlgebra

data SomeSnippet' impl out st algebra parentAlgebra where
    SomeSnippet ::
        Snippet' impl internalSt out st algebra parentAlgebra ->
        SomeSnippet' impl out st algebra parentAlgebra

data RenderedSnippet impl out st algebra where
    RenderedSnippet ::
        !intSt ->
        (RunAlgebra algebra -> st -> IO st -> SnippetUpdater impl intSt out) ->
        (intSt -> IO ()) ->
        RenderedSnippet impl out st algebra

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

emptySnippet :: Snippet' impl () out state algebra parentAlgebra
emptySnippet = Snippet (\_ _ _ pos -> pure (ConstructedSnippet mempty mempty pos pos ()))
                       (\_ _ _ pos () -> pure (ConstructedSnippet mempty mempty pos pos ()))
                       (\_ -> return ())

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
