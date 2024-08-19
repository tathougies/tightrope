{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Web.Tightrope.Types where

import           Control.Applicative
import           Control.Concurrent.MVar
import           Control.Exception (evaluate)
import           Control.Lens
import           Control.Monad.Catch (MonadMask)
import           Control.Monad.IO.Class
import           Control.Monad.Identity
import           Control.Monad.Reader
import           Control.Monad.State
import           Control.Monad.Writer

import           Data.IORef
import           Data.Int
import           Data.Monoid
import           Data.Proxy
import           Data.String
import qualified Data.Text as T
import           Data.Typeable
import           Data.Word
import           Data.JSString (JSString)
import           Data.JSString.Text (textToJSString, textFromJSString)
import           Language.Javascript.JSaddle (FromJSString, MonadJSM(..))

import           System.Mem.StableName

class IsText t where
    fromText :: T.Text -> t
    toText :: t -> T.Text
instance IsText T.Text where
    fromText = id
    toText = id

class AttrValue x where
    type AttrValueState x :: *

    attrValue :: TightropeImpl impl => Proxy impl -> Text impl -> x -> (AttrValueState x, Maybe (Text impl))

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

class RawIO m where
    rawIO :: IO a -> m a

class ( Monoid (Text impl), Eq (Text impl)
      , IsString (Text impl), IsText (Text impl)
#ifdef __GHCJS__
      , IsJSS (Text impl)
#endif
     , FromJSString (Text impl)
     , AttrValue (Text impl)
     , Typeable impl
     , MonadIO (DomM impl), MonadFail (DomM impl), RawIO (DomM impl)
     , MonadMask (DomM impl), MonadDom impl (DomM impl) ) => TightropeImpl impl where
    type Node impl  :: *
    type Text impl  :: *
    data Event impl :: * -> *
    type DomM impl :: * -> *

    createElement  :: Proxy impl -> Text impl -> DomM impl (Node impl)
    createTextNode :: Proxy impl -> Text impl -> DomM impl (Node impl)

    addEventListener :: Node impl -> Event impl e -> ReaderT e (DomM impl) () -> DomM impl (DomM impl ())
    addBodyEventListener :: Event impl e -> ReaderT e (DomM impl) () -> DomM impl (DomM impl ())
    addResizeListener :: Proxy impl -> ((Double, Double) -> DomM impl ()) -> DomM impl (DomM impl ())

    insertAtPos    :: Proxy impl -> DOMInsertPos impl -> Node impl -> DomM impl (DOMInsertPos impl)
    removeChild    :: Proxy impl -> Node impl -> DomM impl ()

    addClasses :: Proxy impl -> Node impl -> Text impl -> DomM impl ()
    enableClass    :: Proxy impl -> Node impl -> Text impl -> DomM impl ()
    disableClass   :: Proxy impl -> Node impl -> Text impl -> DomM impl ()

    setAttribute   :: Proxy impl -> Node impl -> Text impl -> Maybe (Text impl) -> DomM impl ()
    setStyle       :: Proxy impl -> Node impl -> Text impl -> Maybe (Text impl) -> DomM impl ()
    setNodeValue   :: Proxy impl -> Node impl -> Text impl -> DomM impl ()

    requestFrame   :: Proxy impl -> (Double -> DomM impl ()) -> DomM impl ()

    getIORunner :: DomM impl (IORunner impl)

class Monad m => MonadDom impl m where
    liftDom :: Proxy impl -> DomM impl a -> m a

newtype IORunner impl = IORunner (forall a. DomM impl a -> IO a)

type RunAlgebra impl algebra = forall a. algebra a -> DomM impl a
type GenericRunAlgebra impl algebra = forall a m. MonadDom impl m => algebra a -> m a

data EnterExit impl state out m m' = EnterExit (state -> DomM impl ()) (DomM impl state) (RunAlgebra impl m) (RunAlgebra impl m')

newtype RunAlgebraWrapper impl algebra = RunAlgebraWrapper (RunAlgebra impl algebra)
newtype EmbeddedAlgebraWrapper impl algebra (parentAlgebra :: * -> *) =
    EmbeddedAlgebraWrapper (forall a m. MonadDom impl m => algebra a -> m a)
newtype EnterExitT impl state out m a = EnterExitT { runEnterExitT :: EnterExit impl state out m (EnterExitT impl state out m) -> out -> state -> DomM impl (a, state) }

instance (MonadDom impl m, MonadDom impl (DomM impl)) => MonadDom impl (EnterExitT impl st out m) where
    liftDom _ x = EnterExitT $ \_ _ !st -> (,st) <$> liftDom (Proxy @impl) x

instance MonadDom impl m => MonadDom impl (ReaderT r m) where
    liftDom p = lift . liftDom p
instance (MonadDom impl m, Monoid r) => MonadDom impl (WriterT r m) where
    liftDom p = lift . liftDom p
instance MonadDom impl m => MonadDom impl (StateT r m) where
    liftDom p = lift . liftDom p

data DOMInsertPos impl
    = DOMInsertPos
    { insertPosParent :: Node impl
    , insertPosPrevSibling :: Maybe (Node impl) }

newtype AfterAction impl out = AfterAction [ out -> DomM impl () ]

newtype Snippet' impl out state algebra = Snippet (RunAlgebra impl algebra -> state -> DomM impl state -> DOMInsertPos impl -> DomM impl (ConstructedSnippet impl out state algebra))
data ConstructedSnippet impl out state algebra
    = ConstructedSnippet
    { constructedSnippetOut  :: Endo out
    , constructedAfterAction :: AfterAction impl out
    , constructedSiblingPos  :: DOMInsertPos impl
    , constructedChildPos    :: DOMInsertPos impl
    , constructedSnippetNext :: Snippet' impl out state algebra
    , constructedSnippetFinish :: DomM impl () }

newtype Attribute' impl out st algebra = Attribute (Snippet' impl out st algebra)
deriving newtype instance (Monad (DomM impl)) => Monoid (Attribute' impl out st algebra)
deriving newtype instance (Monad (DomM impl)) => Semigroup (Attribute' impl out st algebra)

type GenericSnippet = forall impl st out algebra. TightropeImpl impl => Snippet' impl st out algebra

data Component' impl props (algebra :: * -> *) (parentAlgebra :: * -> *) where
    Component :: (MonadIO parentAlgebra, Typeable state, Typeable out) =>
                 { componentInitState     :: props -> state
                 , componentEmptyOut      :: out
                 , componentRunAlgebra    :: forall a. EnterExit impl state out parentAlgebra algebra -> state -> out -> algebra a -> DomM impl (a, state)
                 , componentOnConstruct   :: RunAlgebra impl algebra -> props -> algebra ()
                 , componentOnPropsUpdate :: props -> algebra ()
                 , componentTemplate      :: Snippet' impl out state algebra }
              -> Component' impl props algebra parentAlgebra

data MountedComponent impl algebra parentAlgebra where
    MountedComponent :: MonadIO parentAlgebra =>
                        { mountedStateV         :: MVar state
                        , mountedOutV           :: IORef out
                        , mountedInsPosV        :: MVar (DOMInsertPos impl, DOMInsertPos impl, DOMInsertPos impl)
                        , mountedEmptyOut       :: out
                        , mountedAlgebraWrapper :: EmbeddedAlgebraWrapper impl algebra parentAlgebra
                        , mountedFinish         :: IO ()
                        , mountedRunAlgebra     :: forall a. EnterExit impl state out parentAlgebra algebra -> state -> out -> algebra a ->  IO (a, state)
                        , mountedTemplate       :: Snippet' impl out state algebra }
                     -> MountedComponent impl algebra parentAlgebra

data Embedded index parent current
    = Embedded { parent :: parent
               , current :: current
               , index :: index }

instance Monoid (AfterAction impl out) where
    mempty = AfterAction []
instance Semigroup (AfterAction impl out) where
    AfterAction a <> AfterAction b = AfterAction (a <> b)

parent_ :: Lens (Embedded idx parent child) (Embedded idx parent' child) parent parent'
parent_ = lens get set
    where get (Embedded parent _ _) = parent
          set (Embedded _ child idx) parent = Embedded parent child idx

current_ :: Lens (Embedded idx parent child) (Embedded idx parent child') child child'
current_ = lens get set
    where get (Embedded _ child _) = child
          set (Embedded parent _ idx) child = Embedded parent child idx

index_ :: Lens (Embedded idx parent child) (Embedded idx' parent child) idx idx'
index_ = lens get set
    where get (Embedded _ _ idx) = idx
          set (Embedded parent child _) idx = Embedded parent child idx

set_ :: Setter' s (Maybe a) -> a -> s -> s
set_ loc val = loc ?~ val

runAfterAction :: Monad (DomM impl) => AfterAction impl out -> out -> DomM impl ()
runAfterAction act out = go' act out
    where go' (AfterAction []) out = pure ()
          go' (AfterAction (x:xs)) out = x out >> go' (AfterAction xs) out

emptySnippet :: Monad (DomM impl) => Snippet' impl out state algebra
emptySnippet = Snippet $ \_ _ _ pos ->
               pure (ConstructedSnippet mempty mempty pos pos emptySnippet (return ()))

instance Monad (DomM impl) => Monoid (Snippet' impl out state m) where
    mempty = emptySnippet

instance Monad (DomM impl) => Semigroup (Snippet' impl out state m) where
    Snippet left <> Snippet right =
        Snippet $ \runAlgebra st getSt siblingPos ->
            do ConstructedSnippet leftOut leftScheduled siblingPos' _ left' finishLeft <-
                   left runAlgebra st getSt siblingPos
               ConstructedSnippet rightOut rightScheduled siblingPos'' childPos right' finishRight <-
                   right runAlgebra st getSt siblingPos'
               pure (ConstructedSnippet (leftOut <> rightOut) (leftScheduled <> rightScheduled)
                                        siblingPos'' childPos (mappend left' right') (finishLeft >> finishRight))

-- * EnterExit monad

instance (Monad m, Monad (DomM impl)) => Functor (EnterExitT impl state out m) where
    fmap f a = do x <- a
                  return (f x)
instance (Monad m, Monad (DomM impl)) => Applicative (EnterExitT impl state out m) where
    pure = return
    f <*> x = do f' <- f
                 x' <- x
                 return (f' x')
instance (Monad m, Monad (DomM impl)) => Monad (EnterExitT impl state out m) where
    a >>= b =
        EnterExitT $ \ee out st ->
        do (x, !st') <- runEnterExitT a ee out st
           runEnterExitT (b x) ee out st'
    return x = EnterExitT $ \_ _ st -> return (x, st)
instance (MonadFail m, MonadFail (DomM impl)) => MonadFail (EnterExitT impl state out m) where
    fail k = EnterExitT $ \_ _ _ -> fail k
instance (Monad m, MonadJSM (DomM impl)) => MonadJSM (EnterExitT impl state out m) where
    liftJSM' f = EnterExitT $ \_ _ !st ->
                 (,st) <$> liftJSM' f
instance (Monad m, MonadIO (DomM impl)) => MonadIO (EnterExitT impl state out m) where
    liftIO f = EnterExitT $ \(EnterExit saveState fetchState runParent _) out !st ->
               do saveState st
                  x <- liftIO f
                  st' <- fetchState
                  return (x, st')
instance (Functor (DomM impl), RawIO (DomM impl)) => RawIO (EnterExitT impl state out m) where
    rawIO f = EnterExitT $ \ee out st ->
              fmap (,st) (rawIO f)
instance (Monad m, Monad (DomM impl)) => MonadReader out (EnterExitT impl state out m) where
    local f act =
        EnterExitT $ \ee out st ->
            runEnterExitT act ee (f out) st
    ask = EnterExitT $ \ee out st -> return (out, st)
instance (Monad m, Monad (DomM impl)) => MonadState state (EnterExitT impl state out m) where
    state f =
        EnterExitT $ \ee out st ->
            pure (f st)

instance RawIO IO where
    rawIO = id
instance (RawIO m, Monad m) => RawIO (ReaderT r m) where
    rawIO = lift . rawIO
instance (RawIO m, Monad m) => RawIO (StateT s m) where
    rawIO = lift . rawIO

getUpdater :: (MonadIO m, Monad (DomM impl))
           => EnterExitT impl state out m (RunAlgebraWrapper impl (EnterExitT impl state out m))
getUpdater = EnterExitT $ \(EnterExit _ _ _ update) out st ->
             pure (RunAlgebraWrapper update, st)

parentComponent :: (MonadIO m, Monad (DomM impl)) => m a -> EnterExitT impl state out m a
parentComponent action =
    EnterExitT $ \(EnterExit saveState fetchState runParent _) out !st ->
    do saveState st
       x <- runParent action
       st' <- fetchState
       return (x, st')

-- * Dummy implementation

data DummyImpl

instance MonadDom DummyImpl IO where
    liftDom _ = id

instance TightropeImpl DummyImpl where
    type Node DummyImpl = ()
    type Text DummyImpl = T.Text
    data Event DummyImpl e = DummyEvent
    type DomM DummyImpl = IO

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
       (oldVal, v) <- liftIO ((,) <$> evaluate oldVal
                                  <*> evaluate v)

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

-- * AttrValue instances

instance AttrValue x => AttrValue (Maybe x) where
    type AttrValueState (Maybe x) = Maybe (AttrValueState x)

    attrValue _ _ Nothing = (Nothing, Nothing)
    attrValue p nm (Just x) =
        let (x', v) = attrValue p nm x
        in (Just x', v)

instance AttrValue String where
    type AttrValueState String = String

    attrValue _ _ x = (x, Just . fromString $ x)

instance AttrValue T.Text where
    type AttrValueState T.Text = T.Text

    attrValue _ _ x = (x, Just . fromText $ x)

instance AttrValue Word where
    type AttrValueState Word = Word

    attrValue _ _ x = (x, Just . fromString . show $ x)

instance AttrValue Int where
    type AttrValueState Int = Int

    attrValue _ _ x = (x, Just . fromString . show $ x)

instance AttrValue Integer where
    type AttrValueState Integer = Integer

    attrValue _ _ x = (x, Just . fromString . show $ x)

instance AttrValue Double where
    type AttrValueState Double = Double

    attrValue _ _ x = (x, Just . fromString . show $ x)

instance AttrValue Float where
    type AttrValueState Float = Float

    attrValue _ _ x = (x, Just . fromString . show $ x)

instance AttrValue Bool where
    type AttrValueState Bool = Bool

    attrValue _ _ False = (False, Nothing)
    attrValue _ name True = (True, Just name)

instance AttrValue x => AttrValue (Identity x) where
    type AttrValueState (Identity x) = AttrValueState x

    attrValue impl nm (Identity v) = attrValue impl nm v
