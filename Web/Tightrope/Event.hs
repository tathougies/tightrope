module Web.Tightrope.Event where

import Web.Tightrope.Types

import Control.Monad.Reader
import Control.Monad.IO.Class

import Data.Proxy

import GHC.TypeLits

on, onBodyEvent ::
    forall impl evt evtName algebra state parentAlgebra.
    TightropeImpl impl => Event impl evt
 -> (GenericRunAlgebra algebra -> state -> ReaderT evt IO ())
 -> Attribute' impl (IO ()) state algebra parentAlgebra
on evt action =
    Attribute set (\_ _ _ -> pure) (\done -> done)
  where
    set :: RunAlgebra algebra -> state -> IO state -> Node impl -> IO (IO ())
    set runAlgebra st getSt n =
        let runAlgebra' :: forall a m. MonadIO m => algebra a -> m a
            runAlgebra' x = liftIO (runAlgebra x)
        in addEventListener n evt (liftIO getSt >>= action runAlgebra')

onBodyEvent evt action =
    Attribute set (\_ _ _ -> pure) (\done -> done)
  where
    set :: RunAlgebra algebra -> state -> IO state -> Node impl -> IO (IO ())
    set runAlgebra st getSt n =
        let runAlgebra' :: forall a m. MonadIO m => algebra a -> m a
            runAlgebra' x = liftIO (runAlgebra x)
        in addBodyEventListener evt (liftIO getSt >>= action runAlgebra')

onWindowResize ::
    forall impl algebra state parentAlgebra. TightropeImpl impl =>
    (GenericRunAlgebra algebra -> state -> (Double, Double) -> IO ())
 -> Attribute' impl (IO ()) state algebra parentAlgebra
onWindowResize action =
    Attribute set (\_ _ _ -> pure) (\done -> done)
  where
    set :: RunAlgebra algebra -> state -> IO state -> Node impl -> IO (IO ())
    set runAlgebra st getSt _ =
        let runAlgebra' :: forall a m. MonadIO m => algebra a -> m a
            runAlgebra' x = liftIO (runAlgebra x)
        in addResizeListener (Proxy :: Proxy impl) $
           \dims -> do
             st <- getSt
             action runAlgebra' st dims
