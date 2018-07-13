{-|
Module      : Hask.Category.Sub
Description : General Sub-Categories
Copyright   : (c) Edward Kmett, 2018
                  Kyle McKean,  2018
License     : BSD-3-Clause
Maintainer  : mckean.kylej@gmail.com
Stability   : experimental
Portability : portatable

__FIXME__: Doc

@since 0.1.0
-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Hask.Category.Sub 
  ( -- * Sub-Categories
    SubCat(..)
  , SubCatOb
  , SubHask
  ) where

import qualified Prelude as Base ()
import Data.Kind (Constraint)

import Data.Constraint (Dict(..))

import Hask.Functor

-- | __FIXME__: Doc
--
-- @since 0.1.0
data SubCat (p :: Cat i) (c :: i -> Constraint) :: Cat i where
  SubCat :: (c a, c b, Ob p a, Ob p b) => { cat :: p a b } -> SubCat p c a b

-- | __FIXME__: Doc
--
-- @since 0.1.0
class (p a, q a) => SubCatOb (p :: i -> Constraint) (q :: i -> Constraint) (a :: i) where
instance (p a, q a) => SubCatOb p q a where

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Category p => Category (SubCat p c) where
  type Ob (SubCat p c) = SubCatOb c (Ob p)
  id = SubCat id
  SubCat f . SubCat g = SubCat (f . g)
  source SubCat{} = Dict
  target SubCat{} = Dict

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Category p => Functor (SubCat p c a) where
  type Dom (SubCat p c a) = SubCat p c
  type Cod (SubCat p c a) = (->)
  fmap = (.)
-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Category p => Functor (SubCat p c) where
  type Dom (SubCat p c) = Yoneda (SubCat p c)
  type Cod (SubCat p c) = Nat (SubCat p c) (->)
  fmap (Yoneda f) = Nat (\g -> g . f)

-- | __FIXME__: Doc
--
-- @since 0.1.0
type SubHask c a b = SubCat (->)
