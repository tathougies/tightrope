{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE CPP #-}

module Main where

#ifdef __GHCJS__
import Web.Tightrope

import Control.Monad.State
import Control.Arrow

import GHCJS.DOM
import GHCJS.DOM.Document hiding (keyDown, click)
import GHCJS.DOM.Element hiding (keyDown, click)
import GHCJS.DOM.EventM hiding (on)
import GHCJS.DOM.HTMLInputElement
import GHCJS.DOM.Types (KeyboardEvent, UIEvent, MouseEvent, uncheckedCastTo)

import qualified Data.Vector as V
import Data.Monoid
import Data.String
import Data.JSString (JSString)

main :: IO ()
main = do Just document <- currentDocument
          Just body <- getBody document

          setCharset document (Just "utf-8" :: Maybe JSString)
          addStylesheet "http://todomvc.com/examples/backbone/node_modules/todomvc-common/base.css"
          addStylesheet "http://todomvc.com/examples/backbone/node_modules/todomvc-app-css/index.css"

          mountComponent (toElement body) todoMvc

data TodoItem = TodoItem { todoItemComplete :: Bool, todoItemName :: String } deriving Show
data TodoItemList = TodoItemList { todoListEditing :: Maybe Int, todoListItems :: V.Vector TodoItem } deriving Show

--todoMvc :: Component (EnterExi TodoItemList IO) IO
todoMvc = statefulComp (TodoItemList Nothing mempty) () (\_ -> pure ()) $
          (div_
          |- (section_ |+ class_ ("todoapp" :: JSString)

             |- (header_ |+ class_ ("todoapp" :: JSString)
                |- (h1_ |- text "todos")
                |- (input_ |+ class_ ("new-todo" :: JSString) |+ placeholder_ ("What needs to be done?" :: JSString) |+ autofocus_ True
                           |+ on keyDown onNewTodo))

             |- (section_ |+ class_ ("main" :: JSString)
                |- (input_ |+ class_ ("toggle-all" :: JSString) |+ type_ ("checkbox" :: JSString)
                           |+ checked_ (\todoList -> V.all todoItemComplete (todoListItems todoList))
                           |+ on click markAllComplete)
                |- (label_ |+ for_ ("toggle-all" :: JSString)
                           |- text "Mark all as complete")

                |- (ul_ |+ class_ ("todo-list" :: JSString)
                        |- repeat_ (V.toList . todoListItems)
                           (li_ |+ dynClass "completed" (todoItemComplete . current)
                                |+ on click startEdit
                                |- (div_ |+ class_ ("view" :: JSString)
                                   |- (input_ |+ class_ ("toggle" :: JSString) |+ type_ ("checkbox" :: JSString) |+ checked_ (todoItemComplete . current)
                                              |+ on click itemToggled)
                                   |- (label_ |- dyn (jss . fromString . todoItemName . current))
                                   |- (button_ |+ class_ ("destroy" :: JSString)
                                               |+ on click deleteItem))
                                |- (input_ |+ class_ ("edit" :: JSString) |+ value_ (jss . fromString . todoItemName . current)))))

             |- (footer_ |+ class_ ("footer" :: JSString)
                         |+ style "display" (\todoList -> if V.null (todoListItems todoList) then "none" else "block" :: JSString)
                |- (span_ |+ class_ ("todo-count" :: JSString)
                   |- dyn (jss . fromString . show . V.length . incompleteItems . todoListItems)
                   |- dyn (\todoList -> if V.length (incompleteItems (todoListItems todoList)) == 1 then " item left" else " items left"))

                |- (ul_ |+ class_ ("filters" :: JSString)
                   |- (li_ |- (a_ |+ class_ ("selected" :: JSString) |+ href_ ("#" :: JSString) |- text "All"))
                   |- (li_ |- (a_ |+ href_ ("#/active" :: JSString) |- text "Active"))
                   |- (li_ |- (a_ |+ href_ ("#/completed"  :: JSString) |- text "Completed")))
                |- (button_ |+ class_ ("clear-completed" :: JSString)
                            |+ style "display" (\todoList -> if V.any todoItemComplete (todoListItems todoList)
                                                             then "block" else "none" :: JSString)
                            |+ on click clearCompleted
                            |- text "Clear completed")))
          |- (footer_ |+ class_ ("info" :: JSString)

             |- (p_ |- text "Double-click to edit a todo")
             |- (p_ |- text "Template by " |- (a_ |+ href_ ("http://sindresorhus.com" :: JSString) |- text "Sindre Sorhus"))
             |- (p_ |- text "Created by "  |- (a_ |+ href_ ("http://todomvc.com" :: JSString) |- text "you"))
             |- (p_ |- text "Part of "     |- (a_ |+ href_ ("http://todomvc.com" :: JSString) |- text "TodoMVC"))))

    where --onNewTodo :: (forall a. StateT TodoItemList IO a -> EventM HTMLInputElement KeyboardEvent a) -> TodoItemList -> EventM HTMLInputElement KeyboardEvent ()
          onNewTodo updateComponent _ =
              do kc <- uiKeyCode
                 Just tgt <- target
                 Just val <- getValue (uncheckedCastTo HTMLInputElement tgt)

                 when (kc == 13) $
                   do liftIO (setValue tgt (Just "" :: Maybe JSString))
                      updateComponent (insertTodoItem val)

--          itemToggled :: (forall a. StateT TodoItemList IO a -> EventM Element MouseEvent a) -> Embedded Int TodoItemList TodoItem -> EventM Element MouseEvent ()
          itemToggled updateComponent cur =
              updateComponent (liftIO (putStrLn ("Item toggled " ++ show (index cur))) >>
                               (modify $ \todoList ->
                                todoList {
                                  todoListItems = todoListItems todoList V.// [(index cur, (current cur) { todoItemComplete = not (todoItemComplete (current cur)) })]
                                }))

          --markAllComplete ::(forall a. StateT TodoItemList IO a -> EventM Element MouseEvent a) -> TodoItemList -> EventM Element MouseEvent ()
          markAllComplete updateComponent _ =
              updateComponent (modify $ \todoList ->
                                   let items' = if V.all todoItemComplete (todoListItems todoList)
                                                then fmap (\item -> item { todoItemComplete = False }) (todoListItems todoList)
                                                else fmap (\item -> item { todoItemComplete = True }) (todoListItems todoList)
                                   in todoList { todoListItems = items' })

          insertTodoItem name = modify $ \todoList -> todoList { todoListItems = todoListItems todoList <> V.singleton (TodoItem False name) }

          incompleteItems = V.filter (not . todoItemComplete)

          clearCompleted updateComponent _ =
              updateComponent (modify $ \todoList -> todoList { todoListItems = V.filter (not . todoItemComplete) (todoListItems todoList) })

          startEdit updateComponent st = updateComponent . modify $ \todoList -> todoList { todoListEditing = Just (index st) }

          deleteItem updateComponent st = updateComponent . modify $ \todoList -> todoList { todoListEditing = Nothing
                                                                                           , todoListItems = uncurry mappend (second tailIfNecy (V.splitAt (index st) (todoListItems todoList))) }
          tailIfNecy x | V.null x = mempty
                       | otherwise = V.tail x
#else

main :: IO ()
main = return ()

#endif
