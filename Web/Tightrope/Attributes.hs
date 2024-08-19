{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Web.Tightrope.Attributes where

import           Web.Tightrope.Types
import           Web.Tightrope.Combinators

import           Control.Monad
import           Control.Monad.Identity

import           Data.Proxy
import qualified Data.Text as T
import           Data.String
import           Data.Monoid

import           GHC.TypeLits

import           Unsafe.Coerce

-- * Classes

-- class_ :: forall impl st algebra parentAlgebra. TightropeImpl impl =>
--           Text impl -> Attribute' impl () st algebra parentAlgebra
-- class_ classNames = Attribute set (\_ _ _ -> pure) (\_ -> pure ())
--     where set :: RunAlgebra algebra -> st -> IO st -> Node impl -> IO ()
--           set _ _ _ n = addClasses (Proxy :: Proxy impl) n classNames

newtype Unit x (unit :: Symbol) = Unit x
data Keyed x st where
    Keyed :: Eq x => (st -> x)
          -> (x -> Maybe T.Text)
          -> Keyed x st
deriving instance Show x => Show (Unit x unit)
deriving instance Eq x => Eq (Unit x unit)
deriving instance Ord x => Ord (Unit x unit)

{-# INLINABLE dynClass #-}
dynClass :: forall impl out st algebra. TightropeImpl impl =>
            Text impl -> (st -> Bool) -> Attribute' impl out st algebra
dynClass className dyn =
    Attribute $
    Snippet (\run st _ pos@(DOMInsertPos n _) -> do
               let enabled = dyn st
               doUpdate enabled n
               pure (ConstructedSnippet mempty mempty pos pos
                                        (update enabled) (pure ())))

  where
    update enabled =
      Snippet (\run st getSt pos@(DOMInsertPos n _) -> do
                 let enabled' = dyn st
                 when (enabled' /= enabled) (doUpdate enabled' n)
                 pure (ConstructedSnippet mempty mempty pos pos
                                          (update enabled') (pure ())))

    doUpdate enabled node
      | enabled = enableClass (Proxy :: Proxy impl) node className
      | otherwise = disableClass (Proxy :: Proxy impl) node className

-- -- * Attributes

-- instance (TightropeImpl impl, AttrValue impl x) => AttrValue impl (st -> x) where
--     type AttrValueState impl (st' -> x) st = FnAttrValueState impl x (st' -> x) st

--     attrValue p attrName st f =
--         let x = f (unsafeCoerce st :: st')
--         in attrValue p attrName st x

data AttributeStrategy = FunctionAttribute
                       | KeyedAttribute
                       | ConstAttribute

type family AttrStrategy x :: AttributeStrategy where
    AttrStrategy (Identity x) = 'ConstAttribute
    AttrStrategy (st -> x)    = 'FunctionAttribute
    AttrStrategy (Keyed x st) = 'KeyedAttribute
    AttrStrategy x            = 'ConstAttribute

class Attrable (strategy :: AttributeStrategy ) x st where
    attr' :: TightropeImpl impl => Proxy strategy
          -> (Proxy impl -> Node impl -> Text impl -> Maybe (Text impl) -> DomM impl ())
          -> Text impl -> x
          -> Attribute' impl out st algebra

instance ( st ~ st', Eq (AttrValueState x)
         , AttrValue x ) =>
    Attrable 'FunctionAttribute (st' -> x) st where

    attr' _ setAttr (name :: Text impl) fn =
        Attribute $ Snippet
        (\run st getSt pos@(DOMInsertPos node _) ->
             do let (key, value) = attrValue p name v
                    v = fn st
                setAttr p node name value
                pure (ConstructedSnippet mempty mempty pos pos
                                         (go key) (pure ())))

        where
          p :: Proxy impl
          p = Proxy

          go oldKey =
            Snippet $ \run st getSt pos@(DOMInsertPos node _) -> do
            let (key, value) = attrValue p name v
                v = fn st
            newKey <- if key /= oldKey
                      then setAttr p node name value >> pure key
                      else pure oldKey
            pure (ConstructedSnippet mempty mempty pos pos (go newKey) (pure ()))

instance st ~ st' => Attrable 'KeyedAttribute (Keyed x st') st where
    attr' _ setAttr name (Keyed mkKey mkValue) =
        Attribute $
        switch_ mkKey $ \key ->
        let Attribute x = attr' (Proxy :: Proxy ConstAttribute) setAttr name (mkValue key)
        in x

--         set :: RunAlgebra algebra -> st -> IO st -> Node impl -> IO x
--         set run st _ node =
--             do let key = mkKey st
--                    v = mkValue key
--                setAttr p node name (fromText <$> v)
--                pure key

--         update :: RunAlgebra algebra -> st -> Node impl -> x -> IO x
--         update _ st node oldKey =
--             let newKey = mkKey st
--                 v = mkValue newKey
--             in if oldKey /= newKey
--                then do setAttr p node name (fromText <$> v)
--                        pure newKey
--                else pure oldKey

instance AttrValue x => Attrable 'ConstAttribute x st where

    attr' _ setAttr (name :: Text impl) v =
        Attribute $
        Snippet (\run st getSt pos@(DOMInsertPos node _) ->
                  let (_, value) = attrValue p name v
                  in setAttr p node name value >>
                     pure (ConstructedSnippet mempty mempty pos pos emptySnippet (pure ())))
      where
        p :: Proxy impl
        p = Proxy

attr :: forall impl strategy x st out algebra.
        ( strategy ~ AttrStrategy x
        , TightropeImpl impl, Attrable strategy x st ) =>
        Text impl -> x
     -> Attribute' impl out st algebra
attr = attr' (Proxy :: Proxy (AttrStrategy x)) setAttribute

-- -- * Styles

style :: forall impl strategy x out st algebra.
        ( strategy ~ AttrStrategy x
        , TightropeImpl impl, Attrable strategy x st ) =>
        Text impl -> x
     -> Attribute' impl out st algebra
style = attr' (Proxy :: Proxy (AttrStrategy x)) setStyle

initialValue_ :: forall impl strategy x out st algebra.
                 ( strategy ~ AttrStrategy x
                 , TightropeImpl impl, Attrable strategy x st ) =>
                 x
              -> Attribute' impl out st algebra
initialValue_ v = keyedAttr_ (\_ -> ()) (attr (fromString "value") v)

keyedAttr_ :: forall impl key out st algebra
            . (Monad (DomM impl), Eq key)
           => (st -> key)
           -> Attribute' impl out st algebra
           -> Attribute' impl out st algebra
keyedAttr_ mkKey (Attribute go) =
    Attribute (keyedUpdates_ mkKey go)

-- * Keyed attributes

-- instance ( TightropeImpl impl, AttrValue impl x, impl ~ impl') => AttrValue impl (Keyed impl' x st') where
--     type AttrValueState impl (Keyed impl' x st') st = AttrValueState impl x st

--     attrValue p nm st (Keyed x mkValue) =
--         let (x', _) = attrValue p nm st x
--         in (x', mkValue x')

keyed :: Eq x => (st -> x) -> (x -> Maybe T.Text) -> Keyed x st
keyed = Keyed

instance (AttrValue x, KnownSymbol unit) =>
    AttrValue (Unit x unit) where

    type AttrValueState (Unit x unit) = AttrValueState x

    attrValue p attrName (Unit x) =
        let (attrSt, val) = attrValue p attrName x
            val' = fmap (<> fromString (symbolVal (Proxy :: Proxy unit))) val
        in (attrSt, val')
