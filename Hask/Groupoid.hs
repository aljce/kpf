{-|
Module      : Hask.Groupoid
Description : A generalized group structure
Copyright   : (c) Edward Kmett, 2018
                  Kyle McKean,  2018
License     : BSD-3-Clause
Maintainer  : mckean.kylej@gmail.com
Stability   : experimental
Portability : portable

__FIXME__: Doc

@since 0.1.0
-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeInType #-}

module Hask.Groupoid 
  ( 
  -- * Groupoids
    Groupoid(..)
  ) where

import Data.Type.Coercion (Coercion)
import Data.Type.Equality ((:~:))

import Hask.Functor

--------------------------------------------------------------------------------
-- * Groupoids
--------------------------------------------------------------------------------

-- | __FIXME__: Doc
--
-- @since 0.1.0
class Category p => Groupoid p where
  -- | __FIXME__: Doc
  --
  -- @since 0.1.0
  sym :: p a b -> p b a
  default sym :: (Op p ~ p) => p a b -> p b a
  sym = op

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance (Category p, Groupoid q) => Groupoid (Nat p q) where
  sym f@Nat{} = Nat (sym (runNat f))

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Groupoid (:~:) where

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Groupoid Coercion where




