{-# LANGUAGE RecordWildCards #-}

module Web.Tightrope.Component where

import Web.Tightrope.Types
import Web.Tightrope.HTML

import Control.Monad
import Control.Monad.IO.Class
import Control.Concurrent.MVar
import Control.Exception (bracket, bracketOnError)

import Data.Monoid
import Data.IORef
import Data.Proxy
import Data.Typeable

import System.Mem.StableName

comp :: (MonadIO parentAlgebra, TightropeImpl impl, Typeable state, Typeable out) =>
        (props -> state) -> out
     -> (forall a. EnterExit state out parentAlgebra algebra -> state -> out -> algebra a -> IO (a, state))
     -> (RunAlgebra algebra -> props -> algebra ())
     -> (props -> algebra ())
     -> Snippet' impl out state algebra
     -> Component' impl props algebra parentAlgebra
comp = Component

statefulComp :: (MonadIO parentAlgebra, TightropeImpl impl, Typeable state, Typeable out) =>
                (props -> state) -> out
             -> (RunAlgebra (EnterExitT state out parentAlgebra) -> props -> EnterExitT state out parentAlgebra ())
             -> (props -> EnterExitT state out parentAlgebra ())
             -> Snippet' impl out state (EnterExitT state out parentAlgebra)
             -> Component' impl props (EnterExitT state out parentAlgebra) parentAlgebra
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
          (st -> EmbeddedAlgebraWrapper childAlgebra algebra -> out -> out)
       -> Component' impl props childAlgebra algebra
       -> (st -> props)
       -> Snippet' impl out st algebra
mount_ setChild (Component { componentTemplate = componentTemplate@(Snippet createTemplate), .. }) mkProps =
    Snippet $ \update st getSt siblingPos ->
    do stVar      <- newEmptyMVar
       outVar     <- newIORef (error "outVar not set")
       intStVar   <- newIORef (error "intStVar not set")
       doneVar    <- newIORef False
       siblingVar <- newEmptyMVar

       isDirtyV   <- newIORef False

       let redraw _ = do isDone <- readIORef doneVar
                         scheduled <-
                             if not isDone
                             then do atomicWriteIORef isDirtyV False

                                     (st, (Snippet updateSnippet, _)) <-
                                         bracket (takeMVar stVar) (putMVar stVar) $ \st ->
                                         (st,) <$> readIORef intStVar

                                     (out, scheduled) <-
                                         bracketOnError (takeMVar siblingVar)
                                                        (putMVar siblingVar) $
                                         \(insPos, _, childPos) -> do
                                           ConstructedSnippet (Endo mkOut) scheduled insPos' childPos updateSnippet' finish' <-
                                               updateSnippet runAlgebra'' st (readMVar stVar) insPos
                                           atomicWriteIORef intStVar (updateSnippet', finish')
                                           putMVar siblingVar (insPos, insPos', childPos)

                                           pure ( mkOut componentEmptyOut
                                                , scheduled )

                                     atomicWriteIORef outVar out
                                     pure (runAfterAction scheduled out)
                             else do
                               atomicWriteIORef isDirtyV False
                               pure (pure ())

                         scheduled

           finish = do isDone <- atomicModifyIORef doneVar (True,)
                       when (not isDone) $ do
                         (st, (_, finishTemplate)) <-
                             bracket (takeMVar stVar) (putMVar stVar) $ \st ->
                             (st,) <$> readIORef intStVar
                         finishTemplate

           runAlgebra'' :: forall a. childAlgebra a -> IO a
           runAlgebra'' a = do isDone <- readIORef doneVar

                               bracketOnError (takeMVar stVar)
                                              (putMVar stVar) $
                                 \st -> do
                                   intSt <- readIORef intStVar
                                   out   <- readIORef outVar
                                   oldStNm <- makeStableName st

                                   let enterExit = EnterExit (\(!st) -> putMVar stVar st) (takeMVar stVar) update runAlgebra''
                                   (x, !st') <- componentRunAlgebra enterExit st out a

                                   if isDone
                                      then putMVar stVar st
                                      else do
                                        putMVar stVar st'

                                        newStNm <- makeStableName st'
                                        when (oldStNm /= newStNm) $ do
                                          wasDirty <- atomicModifyIORef isDirtyV (True,)
                                          when (not wasDirty) (requestFrame (Proxy :: Proxy impl) redraw)
                                   pure x

           updateComponent = Snippet $ \run st getSt insPos ->
                             do (_, insPos', childPos) <- readMVar siblingVar
                                let newProps = mkProps st
                                pure (ConstructedSnippet (Endo (setChild st (EmbeddedAlgebraWrapper (liftIO . runAlgebra''))))
                                                         (AfterAction [ \_ -> runAlgebra'' (componentOnPropsUpdate newProps) ])
                                                         insPos' childPos updateComponent finish)

           initialProps = mkProps st
           initialState = componentInitState initialProps

       putMVar stVar initialState

       ConstructedSnippet (Endo mkOut) scheduled siblingPos' childPos updateSnippet' finish' <-
           createTemplate runAlgebra'' initialState (readMVar stVar) siblingPos

       atomicWriteIORef intStVar (updateSnippet', finish')
       let !initialOut = mkOut componentEmptyOut
       atomicWriteIORef outVar initialOut

       putMVar siblingVar (siblingPos, siblingPos', childPos)

       pure (ConstructedSnippet (Endo (setChild st (EmbeddedAlgebraWrapper (liftIO . runAlgebra''))))
                                (AfterAction [ \_ -> runAfterAction scheduled initialOut
                                             , \_ -> runAlgebra'' (componentOnConstruct runAlgebra'' initialProps)
                                             ])
                                siblingPos' childPos updateComponent finish)
