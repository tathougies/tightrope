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

import System.Mem.StableName

comp :: (MonadIO parentAlgebra, TightropeImpl impl) =>
        (props -> state) -> out
     -> (forall a. EnterExit state out parentAlgebra algebra -> state -> out -> algebra a -> IO (a, state))
     -> (RunAlgebra algebra -> props -> algebra ())
     -> (props -> algebra ())
     -> Snippet' impl internalState out state algebra parentAlgebra
     -> Component' impl props algebra parentAlgebra
comp = Component

statefulComp :: (MonadIO parentAlgebra, TightropeImpl impl) =>
                (props -> state) -> out
             -> (RunAlgebra (EnterExitT state out parentAlgebra) -> props -> EnterExitT state out parentAlgebra ())
             -> (props -> EnterExitT state out parentAlgebra ())
             -> Snippet' impl internalState out state (EnterExitT state out parentAlgebra) parentAlgebra
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

mount_ :: forall impl props st out childAlgebra algebra parentAlgebra.
          (MonadIO algebra, RawIO algebra, TightropeImpl impl) =>
          (st -> EmbeddedAlgebraWrapper childAlgebra algebra -> out -> out)
       -> Component' impl props childAlgebra algebra
       -> (st -> props)
       -> Snippet' impl (MountedComponent impl childAlgebra algebra) out st algebra parentAlgebra
mount_ setChild component mkProps = Snippet createUnder updateElem finish
  where
    createUnder :: RunAlgebra algebra -> st -> IO st -> SnippetConstructor impl (MountedComponent impl childAlgebra algebra) out
    createUnder update st getSt siblingPos =
        case component of
          Component { componentTemplate = componentTemplate@(Snippet { .. })
                    , .. } -> do
            stVar      <- newEmptyMVar
            outVar     <- newIORef (error "outVar not set")
            intStVar   <- newIORef (error "intStVar not set")
            doneVar    <- newIORef False
            siblingVar <- newEmptyMVar

            isDirtyV   <- newIORef False

            let redraw _ = do isDone <- readIORef doneVar
                              scheduled <-
                                  if not isDone
                                  then do atomicWriteIORef isDirtyV False

                                          (st, intSt) <- bracket (takeMVar stVar) (putMVar stVar) $ \st ->
                                                         (st,) <$> readIORef intStVar

                                          (out, scheduled) <-
                                              bracketOnError (takeMVar siblingVar)
                                                             (putMVar siblingVar) $
                                              \(insPos, _, childPos) -> do
                                                ConstructedSnippet (Endo mkOut) scheduled insPos' childPos !intSt' <-
                                                    snippetUpdateElem runAlgebra'' st (readMVar stVar) insPos intSt
                                                atomicWriteIORef intStVar intSt'
                                                putMVar siblingVar (insPos, insPos', childPos)

                                                pure ( mkOut componentEmptyOut
                                                     , scheduled )

                                          atomicWriteIORef outVar out
                                          pure (runAfterAction scheduled out)
                                  else do
                                    atomicWriteIORef isDirtyV False
                                    pure (pure ())

                              scheduled

                intSt = MountedComponent stVar intStVar outVar siblingVar
                                         componentEmptyOut (EmbeddedAlgebraWrapper (liftIO . runAlgebra'')) finish
                                         componentRunAlgebra componentTemplate

                finish = do isDone <- atomicModifyIORef doneVar (True,)
                            when (not isDone) $ do
                              (st, intSt) <- bracket (takeMVar stVar) (putMVar stVar) $ \st ->
                                             (st,) <$> readIORef intStVar
                              snippetFinish intSt

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
                initialProps = mkProps st
                initialState = componentInitState initialProps

            putMVar stVar initialState

            ConstructedSnippet (Endo mkOut) scheduled siblingPos' childPos compIntSt <-
                snippetCreateUnder runAlgebra'' initialState (readMVar stVar) siblingPos

            atomicWriteIORef intStVar compIntSt
            let !initialOut = mkOut componentEmptyOut
            atomicWriteIORef outVar initialOut

            putMVar siblingVar (siblingPos, siblingPos', childPos)

            pure (ConstructedSnippet (Endo (setChild st (EmbeddedAlgebraWrapper (liftIO . runAlgebra''))))
                                     (AfterAction [ \_ -> runAfterAction scheduled initialOut
                                                  , \_ -> runAlgebra'' (componentOnConstruct runAlgebra'' initialProps)
                                                  ])
                                     siblingPos' childPos intSt)

    updateElem run st getSt insPos mc@MountedComponent { .. } =
        do (_, insPos', childPos) <- readMVar mountedInsPosV
           let newProps = mkProps st
           case mountedAlgebraWrapper of
             EmbeddedAlgebraWrapper runAlgebra ->
                 pure (ConstructedSnippet (Endo (setChild st mountedAlgebraWrapper))
                                          (AfterAction [ \_ -> runAlgebra (componentOnPropsUpdate component newProps) ])
                                          insPos' childPos mc)

    finish = mountedFinish
