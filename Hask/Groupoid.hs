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

class Category p => Groupoid p where
  sym :: p a b -> p b a
  default sym :: (Op p ~ p) => p a b -> p b a
  sym = op

instance (Category p, Groupoid q) => Groupoid (Nat p q) where
  sym f@Nat{} = Nat (sym (runNat f))

instance Groupoid (:~:) where
instance Groupoid Coercion where




