module Web.Tightrope.Combinators where

import           Web.Tightrope.Types

import           Control.Monad (forM_)
import           Control.Monad.Reader
import           Control.Lens (Fold, (^?))

import           Data.DList (DList)
import qualified Data.DList as D
import           Data.IORef
import           Data.Maybe
import           Data.Monoid
import           Data.String

import           System.Random

infixl 1 |-, |+

{-# INLINE (|-) #-}
(|-) :: forall impl parent child state out algebra.
        TightropeImpl impl =>
        Snippet' impl out state algebra
     -> Snippet' impl out state algebra
     -> Snippet' impl out state algebra
Snippet parent |- Snippet child =
  Snippet (\runAlgebra st getSt pos -> do
             ConstructedSnippet parentOut parentScheduled siblingPos parentChildPos
                                parent' finishParent <-
               parent runAlgebra st getSt pos
             ConstructedSnippet childOut childScheduled childPos' _
                                child' finishChild <-
               child runAlgebra st getSt parentChildPos
             pure (ConstructedSnippet (parentOut <> childOut) (parentScheduled <> childScheduled)
                                      siblingPos childPos' (parent' |- child') (finishParent >> finishChild)))

{-# INLINE (|+) #-}
(|+) :: TightropeImpl impl =>
        Snippet' impl out state algebra
     -> Attribute' impl out state algebra
     -> Snippet' impl out state algebra
parent |+ Attribute attr = parent |- attr

-- {-# INLINE (|<>) #-}
-- (|<>) :: forall impl state out algebra.
--          TightropeImpl impl =>
--          Snippet' impl out state algebra
--       -> Snippet' impl out state algebra
--       -> Snippet' impl out state algebra
-- Snippet left |<> Snippet right =
--   Snippet $ \runAlgebra st getSt siblingPos ->
--   do ConstructedSnippet leftOut leftScheduled siblingPos' _ left' finishLeft <-
--        left runAlgebra st getSt siblingPos
--      ConstructedSnippet rightOut rightScheduled siblingPos'' childPos right' finishRight <-
--        right runAlgebra st getSt siblingPos'
--      pure (ConstructedSnippet (leftOut <> rightOut) (leftScheduled <> rightScheduled)
--                               siblingPos'' childPos (left' |<> right') (finishLeft >> finishRight))

-- * Projections

project_ :: Monad (DomM impl)
         => (st -> st')
         -> Snippet' impl out st' algebra
         -> Snippet' impl out st  algebra
project_ f (Snippet create) =
    Snippet $ \run st getSt pos ->
    do c <- create run (f st) (f <$> getSt) pos
       pure c { constructedSnippetNext = project_ f (constructedSnippetNext c) }

-- -- * Keyed updates

keyedUpdates_ :: forall impl key state out algebra
               . (Monad (DomM impl), Eq key)
              => (state -> key)
              -> Snippet' impl out state algebra
              -> Snippet' impl out state algebra
keyedUpdates_ mkKey (Snippet create) =
    Snippet (\run st getSt siblingPos -> do
               c <- create run st getSt siblingPos
               let c' = c { constructedSnippetNext = go c' (mkKey st) (constructedSnippetNext c) }
               pure c')
  where
    go oldConstructed oldKey (Snippet nextSnippet) =
      Snippet (\run st getSt siblingPos ->
                 let newKey = mkKey st
                 in if oldKey == newKey
                    then pure oldConstructed
                    else do c <- nextSnippet run st getSt siblingPos
                            let c' = c { constructedSnippetNext = go c' newKey (constructedSnippetNext c) }
                            pure c')
--   where
--     create' :: RunAlgebra algebra -> state -> IO state
--             -> SnippetConstructor impl (key, DOMInsertPos impl, DOMInsertPos impl, Endo out, internalSt) out
--     create' run st getSt siblingPos =
--         do ConstructedSnippet mkOut scheduled siblingPos' pos internalSt <-
--                create run st getSt siblingPos

--            pure (ConstructedSnippet mkOut scheduled siblingPos' pos
--                                     (mkKey st, pos, siblingPos', mkOut, internalSt))

--     update' :: RunAlgebra algebra -> state -> IO state
--             -> SnippetUpdater impl (key, DOMInsertPos impl, DOMInsertPos impl, Endo out, internalSt) out
--     update' run st getSt siblingPos oldSt@(oldKey, oldPos, oldSiblingPos, oldMkOut, oldInternalSt) =
--         let newKey = mkKey st
--         in if oldKey == newKey
--            then pure (ConstructedSnippet oldMkOut mempty
--                                          oldSiblingPos oldPos oldSt)
--            else do ConstructedSnippet mkOut scheduled siblingPos' pos internalSt' <-
--                      update run st getSt siblingPos oldInternalSt
--                    pure (ConstructedSnippet mkOut scheduled siblingPos' pos
--                                             (newKey, pos, siblingPos', mkOut, internalSt'))

--     finish' (_, _, _, _, st) = finish st

-- * Captures

captured_ :: forall impl state out algebra
           . (Monad (DomM impl))
          => (state -> Node impl -> out -> out)
          -> Snippet' impl out state algebra
          -> Snippet' impl out state algebra
captured_ modOut (Snippet snippet) =
    Snippet $ \run st getSt pos ->
    do c <- snippet run st getSt pos
       pure c { constructedSnippetOut = constructedSnippetOut c <>
                                        Endo (modOut st (let DOMInsertPos parent _ = constructedChildPos c
                                                         in parent))
              , constructedSnippetNext = captured_ modOut (constructedSnippetNext c) }

-- -- * Switch

switch_ :: forall key impl state out algebra
         . (Monad (DomM impl), Eq key)
        => (state -> key)
        -> (key -> Snippet' impl out state algebra)
        -> Snippet' impl out state algebra
switch_ mkKey mkComponent =
    Snippet $ \run st getSt pos ->
    do let !initialKey = mkKey st
           Snippet initialComp = mkComponent initialKey

       c <- initialComp run st getSt pos
       pure c { constructedSnippetNext = go initialKey (constructedSnippetFinish c) (constructedSnippetNext c) }

  where

    go oldKey finish (Snippet update) =
        Snippet $ \run st getSt pos ->
        do let !key = mkKey st
           c <- if key == oldKey
                then update run st getSt pos
                else let Snippet nextComp = mkComponent key
                     in finish >>
                        nextComp run st getSt pos
           pure c { constructedSnippetNext = go key (constructedSnippetFinish c) (constructedSnippetNext c) }

--     Snippet create update finish
--   where
--     create :: RunAlgebra algebra -> state -> IO state
--            -> SnippetConstructor impl (key :++ RenderedSnippet impl out state algebra) out
--     create runAlgebra st getSt pos =
--         let !initialKey = mkKey st
--         in case mkComponent st initialKey of
--              SomeSnippet (Snippet create' update' finish') ->
--                do ConstructedSnippet mkOut after siblingPos childPos intSt <-
--                     create' runAlgebra st getSt pos
--                   let intSt' = RenderedSnippet intSt update' finish'
--                   pure (ConstructedSnippet mkOut after siblingPos childPos
--                                            (Initialke :++ intSt'))

--     update :: RunAlgebra algebra -> state -> IO state
--            -> SnippetUpdater impl (key :++ RenderedSnippet impl out state algebra) out
--     update runAlgebra st getSt siblingPos (oldKey :++ rendered) =
--         let !key = mkKey st
--         in case rendered of
--              RenderedSnippet intSt update' finish'
--                  | key == oldKey -> do
--                      ConstructedSnippet mkOut scheduled siblingPos' childPos !intSt' <-
--                        update' runAlgebra st getSt siblingPos intSt
--                      pure (ConstructedSnippet mkOut scheduled siblingPos' childPos
--                                               (key :++ RenderedSnippet intSt' update' finish'))
--                  | otherwise -> do
--                      finish' intSt
--                      case mkComponent st key of
--                        SomeSnippet (Snippet create'' update'' finish'') ->
--                          do ConstructedSnippet mkOut after siblingPos' childPos !intSt <-
--                                create'' runAlgebra st getSt siblingPos
--                             pure (ConstructedSnippet mkOut after siblingPos' childPos
--                                                      (key :++ RenderedSnippet intSt update'' finish''))

--     finish (key :++ RenderedSnippet intSt _ finish') =
--         finish' intSt

-- * Conditionals

cond_ :: Monad (DomM impl)
      => (state -> Bool) -> Snippet' impl out state algebra
      -> Snippet' impl out state algebra
cond_ cond template =
    guarded_ (\s -> if cond s then Just s else Nothing)
             (project_ (\(Embedded _ s _) -> s) template)

data Choice impl out state algebra where
    Choice :: Fold state state'
           -> Snippet' impl out (Embedded () state state') algebra
           -> Choice impl out state algebra

(-->) :: Fold state state'
      -> Snippet' impl out (Embedded () state state') algebra
      -> Choice impl out state algebra
(-->) = Choice

choices_ :: forall impl state out algebra
          . Monad (DomM impl)
         => [ Choice impl out state algebra ]
         -> Snippet' impl out state algebra
choices_ = foldr (\(Choice prism snippet) ->
                      choice_ (\s -> case s ^? prism of
                                       Just x -> Left x
                                       Nothing -> Right ()) snippet .
                      project_ parent) mempty

choice_ :: forall impl a b state out algebra
         . Monad (DomM impl)
        => (state -> Either a b)
        -> Snippet' impl out (Embedded () state a) algebra
        -> Snippet' impl out (Embedded () state b) algebra
        -> Snippet' impl out state algebra
choice_ mkKey aSnippet bSnippet = go aSnippet bSnippet (pure ()) (pure ())
  where
    go ~(Snippet updateA) ~(Snippet updateB) aFinish bFinish =
        Snippet $ \run st getSt siblingPos ->
        case mkKey st of
          Left aSt -> do
            bFinish
            c <- updateA run (Embedded st aSt ()) (getLeft getSt) siblingPos
            pure c { constructedSnippetNext = go (constructedSnippetNext c) bSnippet
                                                 (constructedSnippetFinish c) (pure ()) }
          Right bSt -> do
            aFinish
            c <- updateB run (Embedded st bSt ()) (getRight getSt) siblingPos
            pure c { constructedSnippetNext = go aSnippet (constructedSnippetNext c)
                                                 (pure ()) (constructedSnippetFinish c) }

    getLeft getSt = do
      st <- getSt
      let Left aSt = mkKey st
      pure (Embedded st aSt ())
    getRight getSt = do
      st <- getSt
      let Right bSt = mkKey st
      pure (Embedded st bSt ())

if_ :: Monad (DomM impl)
    => (st -> Bool)
    -> Snippet' impl out st algebra
    -> Snippet' impl out st algebra
    -> Snippet' impl out st algebra
if_ cond true_ false_ =
    choice_ (\s -> if cond s then Left () else Right ())
            (project_ parent true_)
            (project_ parent false_)

guarded_ :: forall impl st st' out algebra
          . (Monad (DomM impl))
         => (st -> Maybe st')
         -> Snippet' impl out (Embedded () st st') algebra
         -> Snippet' impl out st algebra
guarded_ check =
    choice_ (\st -> case check st of
                      Just st -> Right st
                      Nothing -> Left ())
            emptySnippet

-- -- * Repetitions

repeat_ :: forall impl current state out algebra
         . Monad (DomM impl)
        => (state -> [current])
        -> Snippet' impl out (Embedded Int state current) algebra
        -> Snippet' impl out state algebra
repeat_ mkCurrent (Snippet createItem) = go []
  where
    go oldSts =
        Snippet $ \run st getSt siblingPos ->
        do let current = mkCurrent st
               (oldSts', toRemove) = splitAt (length current) oldSts
               toAdd = drop (length oldSts') current

           forM_ toRemove $ \(_, finishItem) -> finishItem

           (mkOut, scheduled, siblingPos', childPos', oldSts'' ) <-
               createAll run st getSt (length oldSts') toAdd =<<
               updateAll run st getSt 0 current (fst <$> oldSts') (mempty, mempty, siblingPos, siblingPos, mempty)

           let oldSts''' = D.toList oldSts''
           pure (ConstructedSnippet mkOut scheduled siblingPos' childPos' (go oldSts''') (mapM_ snd oldSts'''))

    createAll :: RunAlgebra impl algebra -> state -> DomM impl state -> Int -> [current]

              -> ( Endo out, AfterAction impl out, DOMInsertPos impl, DOMInsertPos impl
                 , DList (Snippet' impl out (Embedded Int state current) algebra, DomM impl ()) )

              -> DomM impl ( Endo out, AfterAction impl out, DOMInsertPos impl, DOMInsertPos impl
                           , DList (Snippet' impl out (Embedded Int state current) algebra, DomM impl ()) )
    createAll runAlgebra _ _ !ix [] a = pure a
    createAll runAlgebra state getState !ix (item:items) (mkOut, scheduled, siblingPos', _, a) =
        do ConstructedSnippet itemMkOut itemScheduled siblingPos'' childPos' child' itemFinish <-
               createItem runAlgebra (Embedded state item ix) ((\s -> Embedded s (mkCurrent s !! ix) ix) <$> getState)
                          siblingPos'
           createAll runAlgebra state getState (ix + 1) items
                     ( mkOut <> itemMkOut, scheduled <> itemScheduled, siblingPos''
                     , childPos', a <> pure (child', itemFinish) )

    updateAll :: RunAlgebra impl algebra -> state -> DomM impl state -> Int
              -> [current] -> [Snippet' impl out (Embedded Int state current) algebra]

              -> ( Endo out, AfterAction impl out, DOMInsertPos impl, DOMInsertPos impl
                 , DList (Snippet' impl out (Embedded Int state current) algebra, DomM impl ()) )

              -> DomM impl ( Endo out, AfterAction impl out, DOMInsertPos impl, DOMInsertPos impl
                           , DList (Snippet' impl out (Embedded Int state current) algebra, DomM impl ()) )
    updateAll _ _ _ _ [] _ a = pure a
    updateAll _ _ _ _ _ [] a = pure a
    updateAll run state getState !ix (current:currents) (Snippet updateItem:remaining)
              (mkOut, scheduled, siblingPos, _, a) =
        do ConstructedSnippet itemMkOut itemScheduled siblingPos' childPos' updateItem' itemFinish <-
               updateItem run (Embedded state current ix) ((\s -> Embedded s (mkCurrent s !! ix) ix) <$> getState)
                          siblingPos
           updateAll run state getState (ix + 1) currents remaining
                     ( mkOut <> itemMkOut, scheduled <> itemScheduled, siblingPos'
                     , childPos', a <> pure (updateItem', itemFinish) )

enum_ :: forall impl ix state out algebra
       . (Enum ix, Ord ix, Show ix, Monad (DomM impl))
      => (state -> (ix, ix))
      -> Snippet' impl out (Embedded ix state ix) algebra
      -> Snippet' impl out state algebra
enum_ mkBounds (Snippet create) = go (toEnum 1) (toEnum 0) []
  where
    go oldStart oldEnd oldSts =
        Snippet $ \run st getSt siblingPos ->
        do let (newStart, newEnd) = mkBounds st

               newStartIdx = fromEnum newStart
               newEndIdx   = fromEnum newEnd

               oldStartIdx = fromEnum oldStart
               oldEndIdx   = fromEnum oldEnd

               ( (removeFromBeginning, addToBeginning),
                 (removeFromEnd,       addToEnd) )
                 | newEndIdx < newStartIdx =
                     ( (length oldSts, (succ newStart, newStart)), (0, (succ newEnd, newEnd)) )
                 | newEndIdx < oldStartIdx = -- scrolled up all the way
                     ( (length oldSts, (newStart, newEnd)), (0, (succ newEnd, newEnd)) )
                 | newStartIdx > oldEndIdx = -- scrolled down all the way
                     ( (length oldSts, (newStart, newEnd)), (0, (succ newEnd, newEnd)) )
                 | otherwise =
                     let beginning | newStartIdx < oldStartIdx = ( 0, (newStart, pred oldStart) )
                                   | otherwise = ( newStartIdx - oldStartIdx, (succ newStart, newStart) )
                         end       | newEndIdx > oldEndIdx = ( 0, (succ oldEnd, newEnd) )
                                   | otherwise = ( oldEndIdx - newEndIdx, (succ newEnd, newEnd) )
                     in (beginning, end)

               oldStsLength = length oldSts
               (oldSts', removedFromEnd) = splitAt (oldStsLength - removeFromEnd) oldSts
               (removedFromBeginning, preservedSts) = splitAt removeFromBeginning oldSts'

               preservedCount = oldStsLength - removeFromBeginning - removeFromEnd
               preservedStart = toEnum (oldStartIdx + removeFromBeginning)

           mapM_ snd (removedFromBeginning <> removedFromEnd)

           beginning <- createAll run st getSt (fst addToBeginning) addToBeginning
                                  (mempty, mempty, siblingPos, siblingPos, mempty)
           updated   <- updateAll run st getSt preservedStart (fst <$> preservedSts) beginning

           ( mkOut, scheduled, siblingPos', childPos, oldSts' ) <-
               createAll run st getSt (fst addToEnd) addToEnd updated

           let oldSts'' = D.toList oldSts'
           pure (ConstructedSnippet mkOut scheduled siblingPos' childPos
                                    (go newStart newEnd oldSts'')
                                    (mapM_ snd oldSts''))

    createAll :: RunAlgebra impl algebra -> state -> DomM impl state -> ix -> (ix, ix)
              -> ( Endo out, AfterAction impl out, DOMInsertPos impl, DOMInsertPos impl
                 , DList (Snippet' impl out (Embedded ix state ix) algebra, DomM impl ()))

              -> DomM impl ( Endo out, AfterAction impl out, DOMInsertPos impl, DOMInsertPos impl
                           , DList (Snippet' impl out (Embedded ix state ix) algebra, DomM impl ()))
    createAll run _ _ !ix (start, end) a
        | start > end || ix > end = pure a
    createAll run st getSt ix bounds@(start, end) (mkOut, scheduled, siblingPos, _, a) =
        do ConstructedSnippet itemMkOut itemScheduled siblingPos' childPos' update' finish <-
               create run (Embedded st ix ix) ((\s -> Embedded s ix ix) <$> getSt) siblingPos
           createAll run st getSt (succ ix) bounds
                     (mkOut <> itemMkOut, scheduled <> itemScheduled, siblingPos', childPos', a <> pure ((update', finish)))

    updateAll :: RunAlgebra impl algebra -> state -> DomM impl state -> ix
              -> [ Snippet' impl out (Embedded ix state ix) algebra ]
              -> ( Endo out, AfterAction impl out, DOMInsertPos impl, DOMInsertPos impl
                 , DList (Snippet' impl out (Embedded ix state ix) algebra, DomM impl ()) )

              -> DomM impl ( Endo out, AfterAction impl out, DOMInsertPos impl, DOMInsertPos impl
                           , DList (Snippet' impl out (Embedded ix state ix) algebra, DomM impl ()) )
    updateAll _ _ _ _ [] a = pure a
    updateAll run st getSt ix (Snippet update:items) (mkOut, scheduled, siblingPos, _, a) =
        do ConstructedSnippet itemMkOut itemScheduled siblingPos' childPos' update' finish <-
               update run (Embedded st ix ix) ((\s -> Embedded s ix ix) <$> getSt) siblingPos
           updateAll run st getSt (succ ix) items
                     (mkOut <> itemMkOut, scheduled <> itemScheduled, siblingPos', childPos', a <> pure (update', finish))

-- enum_ :: forall impl ix intSt st out algebra parentAlgebra.
--          (Enum ix, Ord ix, Show ix) =>
--          (st -> (ix, ix))
--       -> Snippet' impl intSt out (Embedded ix st ix) algebra parentAlgebra
--       -> Snippet' impl (ix, ix, [intSt]) out st algebra parentAlgebra
-- enum_ mkBounds (Snippet create update finish) =
--     Snippet create' update' finish'
--   where
--     create' :: RunAlgebra algebra -> st -> IO st -> SnippetConstructor impl (ix, ix, [intSt]) out
--     create' runAlgebra st getSt pos =
--         do let (start, end) = mkBounds st
--            res <- createAll runAlgebra st getSt start (start, end) (ConstructedSnippet mempty mempty pos pos id)
--            pure (res { constructedState = (start, end, constructedState res []) })

--     update' :: RunAlgebra algebra -> st -> IO st -> SnippetUpdater impl (ix, ix, [intSt]) out
--     update' runAlgebra st getSt pos (oldStart, oldEnd, intSts) =
--         do let (newStart, newEnd) = mkBounds st

--                newStartIdx = fromEnum newStart
--                newEndIdx   = fromEnum newEnd

--                oldStartIdx = fromEnum oldStart
--                oldEndIdx   = fromEnum oldEnd

--                ( (removeFromBeginning, addToBeginning),
--                  (removeFromEnd,       addToEnd) )
--                  | newEndIdx < newStartIdx =
--                      ( (length intSts, (succ newStart, newStart)), (0, (succ newEnd, newEnd)) )
--                  | newEndIdx < oldStartIdx = -- scrolled up all the way
--                      ( (length intSts, (newStart, newEnd)), (0, (succ newEnd, newEnd)) )
--                  | newStartIdx > oldEndIdx = -- scrolled down all the way
--                      ( (length intSts, (newStart, newEnd)), (0, (succ newEnd, newEnd)) )
--                  | otherwise =
--                      let beginning | newStartIdx < oldStartIdx = ( 0, (newStart, pred oldStart) )
--                                    | otherwise = ( newStartIdx - oldStartIdx, (succ newStart, newStart) )
--                          end       | newEndIdx > oldEndIdx = ( 0, (succ oldEnd, newEnd) )
--                                    | otherwise = ( oldEndIdx - newEndIdx, (succ newEnd, newEnd) )
--                      in (beginning, end)

--                intStsLength = length intSts
--                (intSts', removedFromEnd) = splitAt (intStsLength - removeFromEnd) intSts
--                (removedFromBeginning, preservedSts) = splitAt removeFromBeginning intSts'

--                preservedCount = intStsLength - removeFromBeginning - removeFromEnd
--                preservedStart = toEnum (oldStartIdx + removeFromBeginning)

--            mapM_ finish (removedFromBeginning <> removedFromEnd)

--            beginning <- createAll runAlgebra st getSt (fst addToBeginning) addToBeginning
--                                   (ConstructedSnippet mempty mempty pos pos id)
--            updated   <- updateAll runAlgebra st getSt preservedStart preservedSts beginning
--            end       <- createAll runAlgebra st getSt (fst addToEnd) addToEnd updated

--            pure (end { constructedState = (newStart, newEnd, constructedState end []) })

--     finish' (_, _, intSts) = mapM_ finish intSts

--     createAll :: RunAlgebra algebra -> st -> IO st -> ix -> (ix, ix)
--               -> ConstructedSnippet impl ([intSt] -> [intSt]) out
--               -> IO (ConstructedSnippet impl ([intSt] -> [intSt]) out)
--     createAll runAlgebra st getSt ix (start, end) a
--         | start > end || ix > end = pure a
--     createAll runAlgebra st getSt ix bounds@(start, end) (ConstructedSnippet mkOut scheduled siblingPos _ a) =
--         do ConstructedSnippet itemMkOut itemScheduled siblingPos' childPos' itemIntSt <-
--                create runAlgebra (Embedded st ix ix) ((\s -> Embedded s ix ix) <$> getSt) siblingPos
--            createAll runAlgebra st getSt (succ ix) bounds
--                      (ConstructedSnippet (mkOut <> itemMkOut) (scheduled <> itemScheduled)
--                                          siblingPos' childPos' (a . (itemIntSt :)))

--     updateAll :: RunAlgebra algebra -> st -> IO st -> ix -> [intSt]
--               -> ConstructedSnippet impl ([intSt] -> [intSt]) out
--               -> IO (ConstructedSnippet impl ([intSt] -> [intSt]) out)
--     updateAll _ _ _ _ [] a = pure a
--     updateAll runAlgebra st getSt ix (item:items) (ConstructedSnippet mkOut scheduled siblingPos _ a) =
--         do ConstructedSnippet itemMkOut itemScheduled siblingPos' childPos' itemIntSt' <-
--                update runAlgebra (Embedded st ix ix) ((\s -> Embedded s ix ix) <$> getSt) siblingPos item
--            updateAll runAlgebra st getSt (succ ix) items
--                      (ConstructedSnippet (mkOut <> itemMkOut) (scheduled <> itemScheduled)
--                                          siblingPos' childPos'
--                                          (a . (itemIntSt' :)))

state_ :: forall impl out state state' algebra
        . MonadIO (DomM impl)
       => (state -> state')
       -> Snippet' impl out state (ReaderT state' algebra)
       -> Snippet' impl out state algebra
state_ mkSubState (Snippet el) =
    Snippet (\runAlgebra st getSt pos -> do
               ref <- liftIO (newIORef (mkSubState st))
               ConstructedSnippet out after sibling child next finish <-
                   el (runAlgebra' ref runAlgebra) st getSt pos
               pure (ConstructedSnippet out after sibling child
                                        (go ref next) finish))
  where
    go ref (Snippet next) =
      Snippet (\runAlgebra st getSt pos -> do
                 ConstructedSnippet out after sibling child next' finish <-
                     next (runAlgebra' ref runAlgebra) st getSt pos
                 pure (ConstructedSnippet out after sibling child
                                          (go ref next') finish))

    runAlgebra' :: forall a. IORef state' -> RunAlgebra impl algebra
                -> ReaderT state' algebra a -> DomM impl a
    runAlgebra' ref run act = do
      x <- liftIO (readIORef ref)
      run (runReaderT act x)

withUniqueName_ :: (IsString (Text impl), MonadIO (DomM impl))
                => Snippet' impl out (Embedded () state (Text impl)) algebra
                -> Snippet' impl out state algebra
withUniqueName_ (Snippet el) =
    Snippet (\runAlgebra st getSt pos -> do
               name <- newName

               ConstructedSnippet out after sibling child next finish <-
                   el runAlgebra (Embedded st name ()) (fmap (\st -> Embedded st name ()) getSt) pos

               pure (ConstructedSnippet out after sibling child
                                        (go name next) finish))

    where
      go name (Snippet next) =
          Snippet (\runAlgebra st getSt pos -> do
                     ConstructedSnippet out after sibling child next finish <-
                         next runAlgebra (Embedded st name ()) (fmap (\st -> Embedded st name ()) getSt) pos

                     pure (ConstructedSnippet out after sibling child
                                              (go name next) finish))

      newName = fmap fromString $
                replicateM 32   $
                randomRIO ('A', 'z')
