{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RecordWildCards #-}

module Web.Tightrope.Component where

import Web.Tightrope.Types
import Web.Tightrope.HTML

import Control.Monad
import Control.Monad.IO.Class
import Control.Concurrent.MVar
import Control.Monad.Catch (bracket, bracketOnError)

import Data.Monoid
import Data.IORef
import Data.Proxy
import Data.Typeable

import System.Mem.StableName

comp :: (MonadIO parentAlgebra, TightropeImpl impl, Typeable state, Typeable out) =>
        (props -> state) -> out
     -> (forall a. EnterExit impl state out parentAlgebra algebra -> state -> out -> algebra a -> DomM impl (a, state))
     -> (RunAlgebra impl algebra -> props -> algebra ())
     -> (props -> algebra ())
     -> Snippet' impl out state algebra
     -> Component' impl props algebra parentAlgebra
comp = Component

statefulComp :: forall impl props state out parentAlgebra
              . (MonadIO parentAlgebra, TightropeImpl impl, Typeable state, Typeable out) =>
                (props -> state) -> out
             -> (RunAlgebra impl (EnterExitT impl state out parentAlgebra) -> props -> EnterExitT impl state out parentAlgebra ())
             -> (props -> EnterExitT impl state out parentAlgebra ())
             -> Snippet' impl out state (EnterExitT impl state out parentAlgebra)
             -> Component' impl props (EnterExitT impl state out parentAlgebra) parentAlgebra
statefulComp st out = comp st out (\enterExit st out a -> runEnterExitT a enterExit out st)

emptyComp :: (MonadIO parentAlgebra, TightropeImpl impl) => Component' impl props parentAlgebra parentAlgebra
emptyComp = comp (\_ -> ()) () (\(EnterExit _ _ runParent _) st _ a -> do { x <- runParent a; return (x, st); }) (\_ _ -> return ()) (\_ -> return()) emptySnippet

mapProps :: (props' -> props) -> Component' impl props algebra parentAlgebra
         -> Component' impl props' algebra parentAlgebra
mapProps f (Component mkSt out runAlgebra construct updateProps template) =
    Component (mkSt . f) out runAlgebra (\update props -> construct update (f props))
              (updateProps . f) template

-- * Mounting support

mount_ :: forall impl props st out childAlgebra algebra.
          (MonadIO algebra, RawIO algebra, TightropeImpl impl) =>
          (st -> EmbeddedAlgebraWrapper impl childAlgebra algebra -> out -> out)
       -> Component' impl props childAlgebra algebra
       -> (st -> props)
       -> Snippet' impl out st algebra
mount_ setChild (Component { componentTemplate = componentTemplate@(Snippet createTemplate), .. }) mkProps =
    Snippet $ \update st getSt siblingPos ->
    do stVar      <- liftIO $ newEmptyMVar
       outVar     <- liftIO $ newIORef (error "outVar not set")
       intStVar   <- liftIO $ newIORef (error "intStVar not set")
       doneVar    <- liftIO $ newIORef False
       siblingVar <- liftIO $ newEmptyMVar

       isDirtyV   <- liftIO $ newIORef False

       let redraw :: Double -> DomM impl ()
           redraw _ = do isDone <- liftIO $ readIORef doneVar
                         scheduled <-
                             if not isDone
                             then do liftIO $ atomicWriteIORef isDirtyV False

                                     (st, (Snippet updateSnippet, _)) <-
                                         liftIO $
                                         bracket (takeMVar stVar) (putMVar stVar) $ \st ->
                                         (st,) <$> readIORef intStVar

                                     (out, scheduled) <-
                                         bracketOnError (liftIO $ takeMVar siblingVar)
                                                        (liftIO . putMVar siblingVar) $
                                         \(insPos, _, childPos) -> do
                                           ConstructedSnippet (Endo mkOut) scheduled insPos' childPos updateSnippet' finish' <-
                                               updateSnippet runAlgebra'' st (liftIO $ readMVar stVar) insPos
                                           liftIO $ do
                                             atomicWriteIORef intStVar (updateSnippet', finish')
                                             putMVar siblingVar (insPos, insPos', childPos)

                                           pure ( mkOut componentEmptyOut
                                                , scheduled )

                                     liftIO $ atomicWriteIORef outVar out
                                     pure (runAfterAction scheduled out)
                             else do
                               liftIO $ atomicWriteIORef isDirtyV False
                               pure (pure ())

                         scheduled

           finish = do isDone <- liftIO (atomicModifyIORef doneVar (True,))
                       when (not isDone) $ do
                         (st, (_, finishTemplate)) <-
                             liftIO $
                             bracket (takeMVar stVar) (putMVar stVar) $ \st ->
                             (st,) <$> readIORef intStVar
                         finishTemplate

           runAlgebra'' :: forall a. childAlgebra a -> DomM impl a
           runAlgebra'' a = do isDone <- liftIO (readIORef doneVar)

                               bracketOnError (liftIO $ takeMVar stVar)
                                              (liftIO . putMVar stVar) $
                                 \st -> do
                                   intSt <- liftIO $ readIORef intStVar
                                   out   <- liftIO $ readIORef outVar
                                   oldStNm <- liftIO $ makeStableName st

                                   let enterExit = EnterExit (\(!st) -> liftIO $ putMVar stVar st) (liftIO $ takeMVar stVar) update runAlgebra''
                                   (x, !st') <- componentRunAlgebra enterExit st out a

                                   if isDone
                                      then liftIO (putMVar stVar st)
                                      else do
                                        liftIO (putMVar stVar st')

                                        newStNm <- liftIO $ makeStableName st'
                                        when (oldStNm /= newStNm) $ do
                                          wasDirty <- liftIO (atomicModifyIORef isDirtyV (True,))
                                          when (not wasDirty) (requestFrame (Proxy :: Proxy impl) redraw)
                                   pure x

           updateComponent = Snippet $ \run st getSt insPos ->
                             do (_, insPos', childPos) <- liftIO (readMVar siblingVar)
                                let newProps = mkProps st
                                pure (ConstructedSnippet (Endo (setChild st (EmbeddedAlgebraWrapper (liftDom (Proxy @impl) . runAlgebra''))))
                                                         (AfterAction [ \_ -> runAlgebra'' (componentOnPropsUpdate newProps) ])
                                                         insPos' childPos updateComponent finish)

           initialProps = mkProps st
           initialState = componentInitState initialProps

       liftIO (putMVar stVar initialState)

       ConstructedSnippet (Endo mkOut) scheduled siblingPos' childPos updateSnippet' finish' <-
           createTemplate runAlgebra'' initialState (liftIO $ readMVar stVar) siblingPos

       liftIO $ do
         atomicWriteIORef intStVar (updateSnippet', finish')
         let !initialOut = mkOut componentEmptyOut
         atomicWriteIORef outVar initialOut

         putMVar siblingVar (siblingPos, siblingPos', childPos)

         pure (ConstructedSnippet (Endo (setChild st (EmbeddedAlgebraWrapper (liftDom (Proxy @impl) . runAlgebra''))))
                                  (AfterAction [ \_ -> runAfterAction scheduled initialOut
                                               , \_ -> runAlgebra'' (componentOnConstruct runAlgebra'' initialProps)
                                               ])
                                  siblingPos' childPos updateComponent finish)
