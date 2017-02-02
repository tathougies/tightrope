module Web.Tightrope.Combinators where

import Web.Tightrope.Types

import Data.Monoid
import Data.Maybe

infixl 1 |-, |-*, |<>, |+

{-# INLINE (|-) #-}
(|-) :: forall impl parent child state out algebra parentAlgebra.
        TightropeImpl impl =>
        Snippet' impl parent out state algebra parentAlgebra
     -> Snippet' impl child out state algebra parentAlgebra
     -> Snippet' impl (parent :++ child) out state algebra parentAlgebra
Snippet createParent updateParent finishParent |- Snippet createChild updateChild finishChild =
  Snippet createUnder' updateElem' finish'
  where createUnder' :: RunAlgebra algebra -> state -> IO state -> SnippetConstructor impl (parent :++ child) out
        createUnder' runAlgebra st getSt pos =
            do ConstructedSnippet parentOut parentScheduled
                                  siblingPos parentChildPos !parentIntSt <-
                                      createParent runAlgebra st getSt pos
               ConstructedSnippet childOut childScheduled
                                  childPos' _ !childIntSt <-
                                      createChild runAlgebra st getSt parentChildPos
               pure (ConstructedSnippet (parentOut <> childOut) (parentScheduled <> childScheduled)
                                        siblingPos childPos' (parentIntSt :++ childIntSt))

        updateElem' :: RunAlgebra algebra -> state -> IO state -> SnippetUpdater impl (parent :++ child) out
        updateElem' runAlgebra st getSt siblingInsertPos (parentIntSt :++ childIntSt) =
            do ConstructedSnippet parentOut parentScheduled
                                  siblingInsertPos' parentChildPos !parentIntSt' <-
                                      updateParent runAlgebra st getSt siblingInsertPos parentIntSt
               ConstructedSnippet childOut childScheduled
                                  childPos' _ !childIntSt' <-
                                      updateChild runAlgebra st getSt parentChildPos childIntSt
               pure (ConstructedSnippet (parentOut <> childOut) (parentScheduled <> childScheduled)
                                        siblingInsertPos' childPos' (parentIntSt' :++ childIntSt'))

        finish' (parentSt :++ childSt) = do
          finishParent parentSt
          finishChild childSt

{-# INLINE (|+) #-}
(|+) :: forall impl el attr state out algebra parentAlgebra.
        TightropeImpl impl =>
        Snippet' impl el out state algebra parentAlgebra
     -> Attribute' impl attr state algebra parentAlgebra
     -> Snippet' impl (el :++ attr) out state algebra parentAlgebra
Snippet createUnder updateElem finishElem |+ Attribute setAttr updateAttr finishAttr =
  Snippet createUnder' updateElem' finish'
  where createUnder' :: RunAlgebra algebra -> state -> IO state -> SnippetConstructor impl (el :++ attr) out
        createUnder' runAlgebra st getSt insertPos =
            do ConstructedSnippet elOut elAfter siblingPos childPos !elIntSt <-
                   createUnder runAlgebra st getSt insertPos
               !attrSt <- setAttr runAlgebra st getSt (insertPosParent childPos)

               pure (ConstructedSnippet elOut elAfter siblingPos childPos
                                        (elIntSt :++ attrSt))

        updateElem' :: RunAlgebra algebra -> state -> IO state -> SnippetUpdater impl (el :++ attr) out
        updateElem' runAlgebra st getSt insertPos (el :++ attr) =
            do ConstructedSnippet elOut elAfter siblingPos childPos !el' <-
                   updateElem runAlgebra st getSt insertPos el
               !attr' <- updateAttr runAlgebra st (insertPosParent childPos) attr
               pure (ConstructedSnippet elOut elAfter siblingPos childPos (el' :++ attr'))

        finish' (el :++ attr) = do
          finishElem el
          finishAttr attr

{-# INLINE (|-*) #-}
(|-*) :: TightropeImpl impl => Snippet' impl parent out state algebra parentAlgebra
      -> SomeSnippet' impl out state algebra parentAlgebra
      -> Snippet' impl (parent :++ RenderedSnippet impl out state algebra) out state algebra parentAlgebra
parent |-* child = parent |- someSnippet_ child

someSnippet_ :: forall impl out state algebra parentAlgebra.
                SomeSnippet' impl out state algebra parentAlgebra
             -> Snippet' impl (RenderedSnippet impl out state algebra) out state algebra parentAlgebra
someSnippet_ (SomeSnippet (Snippet create update finish)) =
    Snippet create' update' finish'
  where
    create' :: RunAlgebra algebra -> state -> IO state -> SnippetConstructor impl (RenderedSnippet impl out state algebra) out
    create' run st getSt pos =
        do ConstructedSnippet mkOut scheduled siblingPos childPos intSt <- create run st getSt pos
           pure (ConstructedSnippet mkOut scheduled siblingPos childPos
                                    (RenderedSnippet intSt update finish))

    update' :: RunAlgebra algebra -> state -> IO state -> SnippetUpdater impl (RenderedSnippet impl out state algebra) out
    update' run st getSt pos (RenderedSnippet intSt update finish) =
        do ConstructedSnippet mkOut scheduled siblingPos' childPos intSt' <-
               update run st getSt pos intSt
           pure (ConstructedSnippet mkOut scheduled siblingPos' childPos
                                    (RenderedSnippet intSt' update finish))

    finish' (RenderedSnippet intSt _ finish) = finish intSt

{-# INLINE (|<>) #-}
(|<>) :: forall impl left right state out algebra parentAlgebra.
         TightropeImpl impl =>
         Snippet' impl left out state algebra parentAlgebra
      -> Snippet' impl right out state algebra parentAlgebra
      -> Snippet' impl (left :++ right) out state algebra parentAlgebra
Snippet createLeft updateLeft finishLeft |<> Snippet createRight updateRight finishRight =
  Snippet createUnder updateElem finish
  where
    createUnder :: RunAlgebra algebra -> state -> IO state -> SnippetConstructor impl (left :++ right) out
    createUnder runAlgebra st getSt siblingPos =
        do ConstructedSnippet leftOut leftScheduled siblingPos' _ !leftIntSt <-
               createLeft runAlgebra st getSt siblingPos
           ConstructedSnippet rightOut rightScheduled siblingPos'' childPos !rightIntSt <-
               createRight runAlgebra st getSt siblingPos'
           pure (ConstructedSnippet (leftOut <> rightOut) (leftScheduled <> rightScheduled)
                                    siblingPos'' childPos (leftIntSt :++ rightIntSt))

    updateElem :: RunAlgebra algebra -> state -> IO state -> SnippetUpdater impl (left :++ right) out
    updateElem runAlgebra st getSt siblingPos (leftIntSt :++ rightIntSt) =
        do ConstructedSnippet leftOut leftScheduled siblingPos' _ !leftIntSt' <-
               updateLeft runAlgebra st getSt siblingPos leftIntSt
           ConstructedSnippet rightOut rightScheduled siblingPos'' childPos !rightIntSt' <-
               updateRight runAlgebra st getSt siblingPos' rightIntSt
           pure (ConstructedSnippet (leftOut <> rightOut) (leftScheduled <> rightScheduled)
                                    siblingPos'' childPos (leftIntSt' :++ rightIntSt'))

    finish (left :++ right) = do
      finishLeft left
      finishRight right

-- * Projections

project_ :: (st -> st')
         -> Snippet' impl intSt out st' algebra parentAlgebra
         -> Snippet' impl intSt out st  algebra parentAlgebra
project_ f (Snippet create update finish) =
    Snippet (\run st getSt pos -> create run (f st) (f <$> getSt) pos)
            (\run st getSt pos intSt -> update run (f st) (f <$> getSt) pos intSt)
            finish

-- * Keyed updates

keyedUpdates_ :: forall impl key internalSt state out algebra parentAlgebra.
                 Eq key => (state -> key)
              -> Snippet' impl internalSt out state algebra parentAlgebra
              -> Snippet' impl (key, DOMInsertPos impl, DOMInsertPos impl, Endo out, internalSt) out state algebra parentAlgebra
keyedUpdates_ mkKey (Snippet create update finish) =
    Snippet create' update' finish'
  where
    create' :: RunAlgebra algebra -> state -> IO state
            -> SnippetConstructor impl (key, DOMInsertPos impl, DOMInsertPos impl, Endo out, internalSt) out
    create' run st getSt siblingPos =
        do ConstructedSnippet mkOut scheduled siblingPos' pos internalSt <-
               create run st getSt siblingPos

           pure (ConstructedSnippet mkOut scheduled siblingPos' pos
                                    (mkKey st, pos, siblingPos', mkOut, internalSt))

    update' :: RunAlgebra algebra -> state -> IO state
            -> SnippetUpdater impl (key, DOMInsertPos impl, DOMInsertPos impl, Endo out, internalSt) out
    update' run st getSt siblingPos oldSt@(oldKey, oldPos, oldSiblingPos, oldMkOut, oldInternalSt) =
        let newKey = mkKey st
        in if oldKey == newKey
           then pure (ConstructedSnippet oldMkOut mempty
                                         oldSiblingPos oldPos oldSt)
           else do ConstructedSnippet mkOut scheduled siblingPos' pos internalSt' <-
                     update run st getSt siblingPos oldInternalSt
                   pure (ConstructedSnippet mkOut scheduled siblingPos' pos
                                            (newKey, pos, siblingPos', mkOut, internalSt'))

    finish' (_, _, _, _, st) = finish st

-- * Captures

captured_ :: forall impl intSt state out algebra parentAlgebra.
             (intSt -> out -> out)
          -> Snippet' impl intSt out state algebra parentAlgebra
          -> Snippet' impl intSt out state algebra parentAlgebra
captured_ modOut (Snippet createUnder updateElem finish) =
    Snippet createUnder' updateElem' finish
    where createUnder' :: RunAlgebra algebra -> state -> IO state -> SnippetConstructor impl intSt out
          createUnder' run st getSt pos =
              do res <- createUnder run st getSt pos
                 pure res { constructedSnippetOut = constructedSnippetOut res <>
                                                    Endo (modOut (constructedState res)) }

          updateElem' :: RunAlgebra algebra -> state -> IO state -> SnippetUpdater impl intSt out
          updateElem' run st getSt pos intSt =
              do res <- updateElem run st getSt pos intSt
                 pure res { constructedSnippetOut = constructedSnippetOut res <>
                                                    Endo (modOut (constructedState res)) }

-- * Switch

switch_ :: forall impl state key out algebra parentAlgebra.
           Eq key => (state -> key)
        -> (state -> key -> SomeSnippet' impl out state algebra parentAlgebra)
        -> Snippet' impl (key :++ RenderedSnippet impl out state algebra) out state algebra parentAlgebra
switch_ mkKey mkComponent =
    Snippet create update finish
  where
    create :: RunAlgebra algebra -> state -> IO state
           -> SnippetConstructor impl (key :++ RenderedSnippet impl out state algebra) out
    create runAlgebra st getSt pos =
        let !initialKey = mkKey st
        in case mkComponent st initialKey of
             SomeSnippet (Snippet create' update' finish') ->
               do ConstructedSnippet mkOut after siblingPos childPos intSt <-
                    create' runAlgebra st getSt pos
                  let intSt' = RenderedSnippet intSt update' finish'
                  pure (ConstructedSnippet mkOut after siblingPos childPos
                                           (initialKey :++ intSt'))

    update :: RunAlgebra algebra -> state -> IO state
           -> SnippetUpdater impl (key :++ RenderedSnippet impl out state algebra) out
    update runAlgebra st getSt siblingPos (oldKey :++ rendered) =
        let !key = mkKey st
        in case rendered of
             RenderedSnippet intSt update' finish'
                 | key == oldKey -> do
                     ConstructedSnippet mkOut scheduled siblingPos' childPos !intSt' <-
                       update' runAlgebra st getSt siblingPos intSt
                     pure (ConstructedSnippet mkOut scheduled siblingPos' childPos
                                              (key :++ RenderedSnippet intSt' update' finish'))
                 | otherwise -> do
                     finish' intSt
                     case mkComponent st key of
                       SomeSnippet (Snippet create'' update'' finish'') ->
                         do ConstructedSnippet mkOut after siblingPos' childPos !intSt <-
                               create'' runAlgebra st getSt siblingPos
                            pure (ConstructedSnippet mkOut after siblingPos' childPos
                                                     (key :++ RenderedSnippet intSt update'' finish''))

    finish (key :++ RenderedSnippet intSt _ finish') =
        finish' intSt

-- * Conditionals

cond_ :: (state -> Bool) -> Snippet' impl childEl out state algebra parentAlgebra
      -> Snippet' impl (Maybe childEl) out state algebra parentAlgebra
cond_ cond template =
    guarded_ (\s -> if cond s then Just s else Nothing)
             (project_ (\(Embedded _ s _) -> s) template)

choice_ :: forall impl aInt bInt a b state out algebra parentAlgebra.
           (state -> Either a b)
        -> Snippet' impl aInt out (Embedded () state a) algebra parentAlgebra
        -> Snippet' impl bInt out (Embedded () state b) algebra parentAlgebra
        -> Snippet' impl (Either aInt bInt) out state algebra parentAlgebra
choice_ mkKey (Snippet aCreate aUpdate aFinish) (Snippet bCreate bUpdate bFinish) =
    Snippet create update finish
  where
    create :: RunAlgebra algebra -> state -> IO state -> SnippetConstructor impl (Either aInt bInt) out
    create run st getSt siblingPos =
        case mkKey st of
          Left aSt -> wrapLeft <$> aCreate run (Embedded st aSt ()) (getLeft getSt) siblingPos
          Right bSt -> wrapRight <$> bCreate run (Embedded st bSt ()) (getRight getSt) siblingPos

    update :: RunAlgebra algebra -> state -> IO state -> SnippetUpdater impl (Either aInt bInt) out
    update run st getSt siblingPos oldSt =
        case (oldSt, mkKey st) of
          (Left oldASt, Left newASt) ->
              wrapLeft <$> aUpdate run (Embedded st newASt ()) (getLeft getSt) siblingPos oldASt
          (Left oldASt, Right newBSt) ->
              aFinish oldASt >>
              (wrapRight <$> bCreate run (Embedded st newBSt ()) (getRight getSt) siblingPos)
          (Right oldBSt, Right newBSt) ->
              wrapRight <$> bUpdate run (Embedded st newBSt ()) (getRight getSt) siblingPos oldBSt
          (Right oldBSt, Left newASt) ->
              bFinish oldBSt >>
              (wrapLeft <$> aCreate run (Embedded st newASt ()) (getLeft getSt) siblingPos)

    finish (Left a) = aFinish a
    finish (Right b) = bFinish b

    getLeft getSt = do
      st <- getSt
      let Left aSt = mkKey st
      pure (Embedded st aSt ())
    getRight getSt = do
      st <- getSt
      let Right bSt = mkKey st
      pure (Embedded st bSt ())

    wrapLeft (ConstructedSnippet mkOut after siblingPos childPos intSt) =
        ConstructedSnippet mkOut after siblingPos childPos (Left intSt)
    wrapRight (ConstructedSnippet mkOut after siblingPos childPos intSt) =
        ConstructedSnippet mkOut after siblingPos childPos (Right intSt)

if_ :: (st -> Bool)
    -> Snippet' impl aInt out st algebra parentAlgebra
    -> Snippet' impl bInt out st algebra parentAlgebra
    -> Snippet' impl (Either aInt bInt) out st algebra parentAlgebra
if_ cond true_ false_ =
    choice_ (\s -> if cond s then Left () else Right ())
            (project_ parent true_)
            (project_ parent false_)

guarded_ :: forall impl st st' child out algebra parentAlgebra.
            (st -> Maybe st')
         -> Snippet' impl child out (Embedded () st st') algebra parentAlgebra
         -> Snippet' impl (Maybe child) out st algebra parentAlgebra
guarded_ check (Snippet create update finish) =
    Snippet createUnder' updateElem' finish'
  where
    createUnder' :: RunAlgebra algebra -> st -> IO st -> SnippetConstructor impl (Maybe child) out
    createUnder' run st getSt siblingPos =
        case check st of
          Just st' ->
              do ConstructedSnippet mkOut scheduled siblingPos' childPos intSt <-
                     create run (Embedded st st' ()) ((\s -> Embedded s (fromJust (check s)) ()) <$> getSt) siblingPos
                 pure (ConstructedSnippet mkOut scheduled siblingPos' childPos (Just intSt))
          Nothing -> pure (ConstructedSnippet mempty mempty siblingPos siblingPos Nothing)
    updateElem' :: RunAlgebra algebra -> st -> IO st -> SnippetUpdater impl (Maybe child) out
    updateElem' run st getSt pos intSt =
        case (check st, intSt) of
          (Nothing, Nothing) ->
              pure (ConstructedSnippet mempty mempty pos pos intSt)
          (Just st', Nothing) ->
              do ConstructedSnippet mkOut scheduled siblingPos' childPos intSt' <-
                     create run (Embedded st st' ()) ((\s -> Embedded s (fromJust (check s)) ()) <$> getSt) pos
                 pure (ConstructedSnippet mkOut scheduled siblingPos' childPos (Just intSt'))
          (Nothing, Just childSt) ->
              do finish childSt
                 pure (ConstructedSnippet mempty mempty pos pos Nothing)
          (Just st', Just childSt) ->
              do ConstructedSnippet mkOut scheduled siblingPos' childPos intSt' <-
                     update run (Embedded st st' ()) ((\s -> Embedded s (fromJust (check s)) ()) <$> getSt)
                            pos childSt
                 pure (ConstructedSnippet mkOut scheduled siblingPos' childPos (Just intSt'))

    finish' Nothing = pure ()
    finish' (Just intSt) = finish intSt


-- * Repetitions

repeat_ :: forall impl intSt current state out algebra parentAlgebra.
           (state -> [current]) -> Snippet' impl intSt out (Embedded Int state current) algebra parentAlgebra
        -> Snippet' impl [intSt] out state algebra parentAlgebra
repeat_ mkCurrent (Snippet createItem updateItem finishItem) =
    Snippet createItems updateItems finishItems
  where
    createItems :: RunAlgebra algebra -> state -> IO state -> SnippetConstructor impl [intSt] out
    createItems runAlgebra state getState siblingPos =
        do let current = mkCurrent state
           createAll runAlgebra state getState 0 current (ConstructedSnippet mempty mempty siblingPos siblingPos id)

    updateItems :: RunAlgebra algebra -> state -> IO state -> SnippetUpdater impl [intSt] out
    updateItems run state getState pos intSt =
        do let current = mkCurrent state
               (intSt', toRemove) = splitAt (length current) intSt
               toAdd = drop (length intSt') current

           mapM_ finishItem toRemove

           createAll run state getState (length intSt') toAdd =<<
             updateAll run state getState 0 current intSt' (ConstructedSnippet mempty mempty pos pos id)

    finishItems = mapM_ finishItem

    createAll :: RunAlgebra algebra -> state -> IO state -> Int -> [current]
              -> ConstructedSnippet impl ([intSt] -> [intSt]) out
              -> IO (ConstructedSnippet impl [intSt] out)
    createAll runAlgebra _ _ !ix [] (ConstructedSnippet mkOut scheduled siblingPos' childPos a) =
        pure (ConstructedSnippet mkOut scheduled siblingPos' childPos (a []))
    createAll runAlgebra state getState !ix (item:items) (ConstructedSnippet mkOut scheduled siblingPos' _ a) =
        do ConstructedSnippet itemMkOut itemScheduled siblingPos'' childPos' itemIntSt <-
               createItem runAlgebra (Embedded state item ix) ((\s -> Embedded s (mkCurrent s !! ix) ix) <$> getState)
                          siblingPos'
           createAll runAlgebra state getState (ix + 1) items
                     (ConstructedSnippet (mkOut <> itemMkOut) (scheduled <> itemScheduled)
                                         siblingPos'' childPos' (a . (itemIntSt:)))

    updateAll :: RunAlgebra algebra -> state -> IO state -> Int
              -> [current] -> [intSt]
              -> ConstructedSnippet impl ([intSt] -> [intSt]) out
              -> IO (ConstructedSnippet impl ([intSt] -> [intSt]) out)
    updateAll _ _ _ _ [] _ a = pure a
    updateAll _ _ _ _ _ [] a = pure a
    updateAll run state getState !ix (current:currents) (itemIntSt:itemIntSts)
              (ConstructedSnippet mkOut scheduled siblingPos _ a) =
        do ConstructedSnippet itemMkOut itemScheduled siblingPos' childPos' itemIntSt' <-
               updateItem run (Embedded state current ix) ((\s -> Embedded s (mkCurrent s !! ix) ix) <$> getState)
                          siblingPos itemIntSt
           updateAll run state getState (ix + 1) currents itemIntSts
                     (ConstructedSnippet (mkOut <> itemMkOut) (scheduled <> itemScheduled)
                                         siblingPos' childPos'
                                         (a . (itemIntSt':)))

enum_ :: forall impl ix intSt st out algebra parentAlgebra.
         (Enum ix, Ord ix, Show ix) =>
         (st -> (ix, ix))
      -> Snippet' impl intSt out (Embedded ix st ix) algebra parentAlgebra
      -> Snippet' impl (ix, ix, [intSt]) out st algebra parentAlgebra
enum_ mkBounds (Snippet create update finish) =
    Snippet create' update' finish'
  where
    create' :: RunAlgebra algebra -> st -> IO st -> SnippetConstructor impl (ix, ix, [intSt]) out
    create' runAlgebra st getSt pos =
        do let (start, end) = mkBounds st
           res <- createAll runAlgebra st getSt start (start, end) (ConstructedSnippet mempty mempty pos pos id)
           pure (res { constructedState = (start, end, constructedState res []) })

    update' :: RunAlgebra algebra -> st -> IO st -> SnippetUpdater impl (ix, ix, [intSt]) out
    update' runAlgebra st getSt pos (oldStart, oldEnd, intSts) =
        do let (newStart, newEnd) = mkBounds st

               newStartIdx = fromEnum newStart
               newEndIdx   = fromEnum newEnd

               oldStartIdx = fromEnum oldStart
               oldEndIdx   = fromEnum oldEnd

               ( (removeFromBeginning, addToBeginning),
                 (removeFromEnd,       addToEnd) )
                 | newEndIdx < newStartIdx =
                     ( (length intSts, (succ newStart, newStart)), (0, (succ newEnd, newEnd)) )
                 | newEndIdx < oldStartIdx = -- scrolled up all the way
                     ( (length intSts, (newStart, newEnd)), (0, (succ newEnd, newEnd)) )
                 | newStartIdx > oldEndIdx = -- scrolled down all the way
                     ( (length intSts, (newStart, newEnd)), (0, (succ newEnd, newEnd)) )
                 | otherwise =
                     let beginning | newStartIdx < oldStartIdx = ( 0, (newStart, pred oldStart) )
                                   | otherwise = ( newStartIdx - oldStartIdx, (succ newStart, newStart) )
                         end       | newEndIdx > oldEndIdx = ( 0, (succ oldEnd, newEnd) )
                                   | otherwise = ( oldEndIdx - newEndIdx, (succ newEnd, newEnd) )
                     in (beginning, end)

               intStsLength = length intSts
               (intSts', removedFromEnd) = splitAt (intStsLength - removeFromEnd) intSts
               (removedFromBeginning, preservedSts) = splitAt removeFromBeginning intSts'

               preservedCount = intStsLength - removeFromBeginning - removeFromEnd
               preservedStart = toEnum (oldStartIdx + removeFromBeginning)

           mapM_ finish (removedFromBeginning <> removedFromEnd)

           beginning <- createAll runAlgebra st getSt (fst addToBeginning) addToBeginning
                                  (ConstructedSnippet mempty mempty pos pos id)
           updated   <- updateAll runAlgebra st getSt preservedStart preservedSts beginning
           end       <- createAll runAlgebra st getSt (fst addToEnd) addToEnd updated

           pure (end { constructedState = (newStart, newEnd, constructedState end []) })

    finish' (_, _, intSts) = mapM_ finish intSts

    createAll :: RunAlgebra algebra -> st -> IO st -> ix -> (ix, ix)
              -> ConstructedSnippet impl ([intSt] -> [intSt]) out
              -> IO (ConstructedSnippet impl ([intSt] -> [intSt]) out)
    createAll runAlgebra st getSt ix (start, end) a
        | start > end || ix > end = pure a
    createAll runAlgebra st getSt ix bounds@(start, end) (ConstructedSnippet mkOut scheduled siblingPos _ a) =
        do ConstructedSnippet itemMkOut itemScheduled siblingPos' childPos' itemIntSt <-
               create runAlgebra (Embedded st ix ix) ((\s -> Embedded s ix ix) <$> getSt) siblingPos
           createAll runAlgebra st getSt (succ ix) bounds
                     (ConstructedSnippet (mkOut <> itemMkOut) (scheduled <> itemScheduled)
                                         siblingPos' childPos' (a . (itemIntSt :)))

    updateAll :: RunAlgebra algebra -> st -> IO st -> ix -> [intSt]
              -> ConstructedSnippet impl ([intSt] -> [intSt]) out
              -> IO (ConstructedSnippet impl ([intSt] -> [intSt]) out)
    updateAll _ _ _ _ [] a = pure a
    updateAll runAlgebra st getSt ix (item:items) (ConstructedSnippet mkOut scheduled siblingPos _ a) =
        do ConstructedSnippet itemMkOut itemScheduled siblingPos' childPos' itemIntSt' <-
               update runAlgebra (Embedded st ix ix) ((\s -> Embedded s ix ix) <$> getSt) siblingPos item
           updateAll runAlgebra st getSt (succ ix) items
                     (ConstructedSnippet (mkOut <> itemMkOut) (scheduled <> itemScheduled)
                                         siblingPos' childPos'
                                         (a . (itemIntSt' :)))
