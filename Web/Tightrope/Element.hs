module Web.Tightrope.Element
    ( el, text, dyn, dynText, dyn')
        where

import Control.Monad

import Data.Proxy
import Data.String
import qualified Data.Text as T

import Web.Tightrope.Types

constNodeSnippet :: Node impl -> IO ()
                 -> Snippet' impl st out algebra
constNodeSnippet n finish =
    Snippet $ \_ _ _ (DOMInsertPos parent _) ->
        pure (ConstructedSnippet mempty mempty
                                 (DOMInsertPos parent (Just n))
                                 (DOMInsertPos n Nothing)
                                 (constNodeSnippet n finish) finish)

-- * HTML elements

el :: forall impl st out algebra.
      TightropeImpl impl =>
      Text impl -> Snippet' impl st out algebra
el tagName = Snippet $ \_ _ _ insertPos ->
             do el <- createElement p tagName

                insertPos' <- insertAtPos p insertPos el
                pure (ConstructedSnippet mempty mempty
                                         insertPos'
                                         (DOMInsertPos el Nothing)
                                         (constNodeSnippet el (removeChild p el))
                                         (removeChild p el))

  where
    p :: Proxy impl
    p = Proxy

-- * Text

text :: forall impl st out algebra.
        TightropeImpl impl =>
        Text impl
     -> Snippet' impl st out algebra
text str = Snippet $ \_ _ _ insertPos ->
           do txt <- createTextNode p str
              insertPos' <- insertAtPos p insertPos txt
              pure (ConstructedSnippet mempty mempty insertPos'
                                       (DOMInsertPos txt Nothing)
                                       (constNodeSnippet txt (removeChild p txt))
                                       (removeChild p txt))
  where
    p :: Proxy impl
    p = Proxy

-- Orphan in this module, but not in the library
instance TightropeImpl impl => IsString (Snippet' impl st out algebra) where
    fromString x = text (fromString x)

dyn :: TightropeImpl impl => (st -> Text impl) -> Snippet' impl out st algebra
dyn = dyn' id

dynText :: TightropeImpl impl => (st -> T.Text) -> Snippet' impl out st algebra
dynText = dyn' fromText

dyn' :: forall s impl st out algebra.
        (TightropeImpl impl, Eq s) =>
        (s -> Text impl)
     -> (st -> s) -> Snippet' impl out st algebra
dyn' toString fromState = Snippet $ \_ st _ insertPos ->
                          do let str = toString stInt
                                 stInt = fromState st

                             txt <- createTextNode p str

                             insertPos' <- insertAtPos p insertPos txt

                             let finish = removeChild p txt
                                 continue' oldStInt =
                                     Snippet $ \_ st _ (DOMInsertPos parent _) ->
                                     do let str' = toString stInt
                                            stInt = fromState st
                                        when (oldStInt /= stInt) $
                                             setNodeValue p txt str'
                                        pure (ConstructedSnippet mempty mempty
                                                                 (DOMInsertPos parent (Just txt))
                                                                 (DOMInsertPos txt Nothing)
                                                                 (continue' stInt) finish)

                             pure (ConstructedSnippet mempty mempty
                                                      insertPos'
                                                      (DOMInsertPos txt Nothing)
                                                      (continue' stInt) finish)
  where
    p :: Proxy impl
    p = Proxy

    -- createUnder _ st _ insertPos =
    --     do let str = toString strInt
    --            strInt = fromState st

    --        txt <- createTextNode p str

    --        insertPos' <- insertAtPos p insertPos txt
    --        pure (ConstructedSnippet mempty mempty
    --                                 insertPos'
    --                                 (DOMInsertPos txt Nothing)
    --                                 (txt :++ strInt))

    -- updateElem _ st _ (DOMInsertPos parent _) (txt :++ oldStInt) =
    --     do let str' = toString stInt
    --            stInt = fromState st
    --        when (oldStInt /= stInt) $
    --             setNodeValue p txt str'
    --        pure (ConstructedSnippet mempty mempty
    --                                 (DOMInsertPos parent (Just txt))
    --                                 (DOMInsertPos txt Nothing)
    --                                 (txt :++ stInt))

    -- finish (txt :++ _) =
    --     removeChild p txt
