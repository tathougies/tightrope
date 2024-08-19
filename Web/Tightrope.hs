{-# LANGUAGE CPP #-}

module Web.Tightrope
    ( module Web.Tightrope.Attributes
    , module Web.Tightrope.Element
    , module Web.Tightrope.Combinators
    , module Web.Tightrope.Component
    , module Web.Tightrope.Event
    , module Web.Tightrope.Lifecycle

    , module Web.Tightrope.HTML
    , module Web.Tightrope.HTML.Attributes

    , module Web.Tightrope.Types

#ifdef __GHCJS__
    , module Web.Tightrope.JS
#else
    , module Web.Tightrope.Static
#endif
    ) where

import Web.Tightrope.Attributes
import Web.Tightrope.Element
import Web.Tightrope.Combinators
import Web.Tightrope.Component
import Web.Tightrope.Event
import Web.Tightrope.Lifecycle

import Web.Tightrope.HTML hiding (style_, title_)
import Web.Tightrope.HTML.Attributes hiding (cite_, dir_, form_, label_, span_, em_)

import Web.Tightrope.Types hiding ( Node, RunAlgebra, EnterExit, EnterExitT
                                  , GenericRunAlgebra, EmbeddedAlgebraWrapper
                                  , liftDom )

#ifdef __GHCJS__
import Web.Tightrope.JS hiding (drop)
#else
import Web.Tightrope.Static
#endif
