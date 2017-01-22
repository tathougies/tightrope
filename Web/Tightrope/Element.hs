module Web.Tightrope.Element where

import Control.Monad

import Data.Proxy
import qualified Data.Text as T

import Web.Tightrope.Types

-- * HTML elements

el :: forall impl st out algebra parentAlgebra.
      TightropeImpl impl =>
      Text impl -> Snippet' impl (Node impl) st out algebra parentAlgebra
el tagName = Snippet createUnder updateElem finish
  where
    p :: Proxy impl
    p = Proxy

    createUnder _ _ _ insertPos =
        do el <- createElement p tagName

           insertPos' <- insertAtPos p insertPos el
           pure (ConstructedSnippet mempty mempty
                                    insertPos' (DOMInsertPos el Nothing)
                                    el)

    updateElem _ _ _ (DOMInsertPos parent _) el =
        pure (ConstructedSnippet mempty mempty
                                 (DOMInsertPos parent (Just el))
                                 (DOMInsertPos el Nothing)
                                 el)

    finish = removeChild p

-- * Text

text :: forall impl st out algebra parentAlgebra.
        TightropeImpl impl =>
        Text impl
     -> Snippet' impl (Node impl) st out algebra parentAlgebra
text str = Snippet createUnder updateElem finish
  where
    p :: Proxy impl
    p = Proxy

    createUnder _ _ _ insertPos =
        do txt <- createTextNode p str

           insertPos' <- insertAtPos p insertPos txt
           pure (ConstructedSnippet mempty mempty insertPos'
                                    (DOMInsertPos txt Nothing) txt)

    updateElem _ _ _ (DOMInsertPos parent _) el =
        pure (ConstructedSnippet mempty mempty
                                 (DOMInsertPos parent (Just el))
                                 (DOMInsertPos parent Nothing)
                                 el)

    finish = removeChild p

dyn :: TightropeImpl impl => (st -> Text impl) -> Snippet' impl (Node impl :++ Text impl) out st algebra parentAlgebra
dyn = dyn' id

dynText :: TightropeImpl impl => (st -> T.Text) -> Snippet' impl (Node impl :++ T.Text) out st algebra parentAlgebra
dynText = dyn' fromText

dyn' :: forall s impl st out algebra parentAlgebra.
        (TightropeImpl impl, Eq s) =>
        (s -> Text impl)
     -> (st -> s) -> Snippet' impl (Node impl :++ s) out st algebra parentAlgebra
dyn' toString fromState = Snippet createUnder updateElem finish
  where
    p :: Proxy impl
    p = Proxy

    createUnder _ st _ insertPos =
        do let str = toString strInt
               strInt = fromState st

           txt <- createTextNode p str

           insertPos' <- insertAtPos p insertPos txt
           pure (ConstructedSnippet mempty mempty
                                    insertPos'
                                    (DOMInsertPos txt Nothing)
                                    (txt :++ strInt))

    updateElem _ st _ (DOMInsertPos parent _) (txt :++ oldStInt) =
        do let str' = toString stInt
               stInt = fromState st
           when (oldStInt /= stInt) $
                setNodeValue p txt str'
           pure (ConstructedSnippet mempty mempty
                                    (DOMInsertPos parent (Just txt))
                                    (DOMInsertPos txt Nothing)
                                    (txt :++ stInt))

    finish (txt :++ _) =
        removeChild p txt
