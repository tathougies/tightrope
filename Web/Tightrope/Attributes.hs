{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}

module Web.Tightrope.Attributes where

import Web.Tightrope.Types

import Control.Monad

import qualified Data.Text as T
import Data.Proxy
import Data.String
import Data.Word
import Data.Monoid

import GHC.TypeLits

import Unsafe.Coerce

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
dynClass :: forall impl st algebra parentAlgebra. TightropeImpl impl =>
            Text impl -> (st -> Bool) -> Attribute' impl Bool st algebra parentAlgebra
dynClass className dyn = Attribute set update (\_ -> pure ())
    where set :: RunAlgebra algebra -> st -> IO st -> Node impl -> IO Bool
          set update st _ node =
              do let enabled = dyn st
                 doUpdate enabled node
                 pure enabled

          update runAlgebra st node enabled =
              do let enabled' = dyn st
                 when (enabled' /= enabled) (doUpdate enabled' node)
                 pure enabled'

          doUpdate enabled node
              | enabled = enableClass (Proxy :: Proxy impl) node className
              | otherwise = disableClass (Proxy :: Proxy impl) node className

-- * Attributes

class AttrValue x where
    type AttrValueState x :: *

    attrValue :: TightropeImpl impl => Proxy impl -> Text impl -> x -> (AttrValueState x, Maybe (Text impl))

instance AttrValue x => AttrValue (Maybe x) where
    type AttrValueState (Maybe x) = Maybe (AttrValueState x)

    attrValue _ _ Nothing = (Nothing, Nothing)
    attrValue p nm (Just x) =
        let (x', v) = attrValue p nm x
        in (Just x', v)

instance AttrValue String where
    type AttrValueState String = String

    attrValue _ _ x = (x, Just . fromString $ x)

instance AttrValue T.Text where
    type AttrValueState T.Text = T.Text

    attrValue _ _ x = (x, Just . fromText $ x)

instance AttrValue Word where
    type AttrValueState Word = Word

    attrValue _ _ x = (x, Just . fromString . show $ x)

instance AttrValue Int where
    type AttrValueState Int = Int

    attrValue _ _ x = (x, Just . fromString . show $ x)

instance AttrValue Integer where
    type AttrValueState Integer = Integer

    attrValue _ _ x = (x, Just . fromString . show $ x)

instance AttrValue Double where
    type AttrValueState Double = Double

    attrValue _ _ x = (x, Just . fromString . show $ x)

instance AttrValue Float where
    type AttrValueState Float = Float

    attrValue _ _ x = (x, Just . fromString . show $ x)

instance (AttrValue x, KnownSymbol unit) =>
    AttrValue (Unit x unit) where

    type AttrValueState (Unit x unit) = AttrValueState x

    attrValue p attrName (Unit x) =
        let (attrSt, val) = attrValue p attrName x
            val' = fmap (<> fromString (symbolVal (Proxy :: Proxy unit))) val
        in (attrSt, val')

instance AttrValue Bool where
    type AttrValueState Bool = Bool

    attrValue _ _ False = (False, Nothing)
    attrValue _ name True = (True, Just name)

-- instance (TightropeImpl impl, AttrValue impl x) => AttrValue impl (st -> x) where
--     type AttrValueState impl (st' -> x) st = FnAttrValueState impl x (st' -> x) st

--     attrValue p attrName st f =
--         let x = f (unsafeCoerce st :: st')
--         in attrValue p attrName st x

data AttributeStrategy = FunctionAttribute
                       | KeyedAttribute
                       | ConstAttribute

type family AttrStrategy x :: AttributeStrategy where
    AttrStrategy (st -> x)    = 'FunctionAttribute
    AttrStrategy (Keyed x st) = 'KeyedAttribute
    AttrStrategy x            = 'ConstAttribute

class Attrable (strategy :: AttributeStrategy ) x st where

    type AttrableState strategy x st :: *

    attr' :: TightropeImpl impl => Proxy strategy
          -> (Proxy impl -> Node impl -> Text impl -> Maybe (Text impl) -> IO ())
          -> Text impl -> x
          -> Attribute' impl (AttrableState strategy x st) st algebra parentAlgebra

instance ( st ~ st', Eq (AttrValueState x)
         , AttrValue x ) =>
    Attrable 'FunctionAttribute (st' -> x) st where

    type AttrableState 'FunctionAttribute (st' -> x) st = AttrValueState x

    attr' _ setAttr (name :: Text impl) fn = Attribute set update (\_ -> pure ())
      where
        p :: Proxy impl
        p = Proxy

        set :: RunAlgebra algebra -> st -> IO st -> Node impl -> IO (AttrValueState x)
        set run st _ node =
            do let (key, value) = attrValue p name v
                   v = fn st
               setAttr p node name value
               pure key

        update :: RunAlgebra algebra -> st -> Node impl -> AttrValueState x -> IO (AttrValueState x)
        update _ st node oldKey = do
          let (key, value) = attrValue p name v
              v = fn st
          if key /= oldKey
            then do
              setAttr p node name value
              pure key
            else pure oldKey

instance st ~ st' => Attrable 'KeyedAttribute (Keyed x st') st where
    type AttrableState 'KeyedAttribute (Keyed x st') st = x

    attr' _ setAttr (name :: Text impl) (Keyed mkKey mkValue) = Attribute set update (\_ -> pure ())
      where
        p :: Proxy impl
        p = Proxy

        set :: RunAlgebra algebra -> st -> IO st -> Node impl -> IO x
        set run st _ node =
            do let key = mkKey st
                   v = mkValue key
               setAttr p node name (fromText <$> v)
               pure key

        update :: RunAlgebra algebra -> st -> Node impl -> x -> IO x
        update _ st node oldKey =
            let newKey = mkKey st
                v = mkValue newKey
            in if oldKey /= newKey
               then do setAttr p node name (fromText <$> v)
                       pure newKey
               else pure oldKey

instance AttrValue x => Attrable 'ConstAttribute x st where
    type AttrableState 'ConstAttribute x st = ()

    attr' _ setAttr (name :: Text impl) v = Attribute set (\_ _ _ -> pure) (\_ -> pure ())
      where
        p :: Proxy impl
        p = Proxy

        set :: RunAlgebra algebra -> st -> IO st -> Node impl -> IO ()
        set run st _ node =
            let (_, value) = attrValue p name v
            in setAttr p node name value

attr :: forall impl strategy x st algebra parentAlgebra.
        ( strategy ~ AttrStrategy x
        , TightropeImpl impl, Attrable strategy x st ) =>
        Text impl -> x
     -> Attribute' impl (AttrableState strategy x st) st algebra parentAlgebra
attr = attr' (Proxy :: Proxy (AttrStrategy x)) setAttribute

-- * Styles

style :: forall impl strategy x st algebra parentAlgebra.
        ( strategy ~ AttrStrategy x
        , TightropeImpl impl, Attrable strategy x st ) =>
        Text impl -> x
     -> Attribute' impl (AttrableState strategy x st) st algebra parentAlgebra
style = attr' (Proxy :: Proxy (AttrStrategy x)) setStyle

initialValue_ :: forall impl strategy x st algebra parentAlgebra.
                 ( strategy ~ AttrStrategy x
                 , TightropeImpl impl, Attrable strategy x st ) =>
                 x
              -> Attribute' impl (() :++ AttrableState strategy x st) st algebra parentAlgebra
initialValue_ v = keyedAttr_ (\_ -> ()) (attr (fromString "value") v)

keyedAttr_ :: forall impl key attrSt st algebra parentAlgebra.
              Eq key => (st -> key)
           -> Attribute' impl attrSt st algebra parentAlgebra
           -> Attribute' impl (key :++ attrSt) st algebra parentAlgebra
keyedAttr_ mkKey (Attribute set update finish) =
    Attribute set' update' finish'
    where
      set' :: RunAlgebra algebra -> st -> IO st -> Node impl -> IO (key :++ attrSt)
      set' run st getSt node = do
        let initialKey = mkKey st
        (initialKey :++) <$> set run st getSt node

      update' :: RunAlgebra algebra -> st -> Node impl -> (key :++ attrSt) -> IO (key :++ attrSt)
      update' run st node oldSt'@(oldKey :++ oldSt) =
          let newKey = mkKey st
          in if newKey == oldKey
             then return oldSt'
             else (newKey :++) <$> update run st node oldSt

      finish' (_ :++ attrSt) = finish attrSt

-- * Keyed attributes

-- instance ( TightropeImpl impl, AttrValue impl x, impl ~ impl') => AttrValue impl (Keyed impl' x st') where
--     type AttrValueState impl (Keyed impl' x st') st = AttrValueState impl x st

--     attrValue p nm st (Keyed x mkValue) =
--         let (x', _) = attrValue p nm st x
--         in (x', mkValue x')

keyed :: Eq x => (st -> x) -> (x -> Maybe T.Text) -> Keyed x st
keyed = Keyed
