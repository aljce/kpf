{-|
Module      : Hask.Functor.Faithful
Description : Fully faithful functors
Copyright   : (c) Edward Kmett, 2018
                  Kyle McKean,  2018
License     : BSD-3-Clause
Maintainer  : mckean.kylej@gmail.com
Stability   : experimental
Portability : portable

__FIXME__: Doc

@since 0.1.0
-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeInType #-}
module Hask.Functor.Faithful 
  (
  -- * Fully Faithful Functors 
  FullyFaithful(..)
  ) where

import qualified Prelude ()

import Data.Constraint (Dict, (:-), unmapDict)

import Hask.Functor

-- | __FIXME__: Doc
--
-- @since 0.1.0
class Functor f => FullyFaithful (f :: i -> j) where
  -- | __FIXME__: Doc
  --
  -- @since 0.1.0
  unfmap :: Cod f (f a) (f b) -> Dom f a b

instance FullyFaithful Dict where
  unfmap = unmapDict

instance FullyFaithful (->) where
  unfmap (Nat f) = Yoneda (f id)

instance FullyFaithful (:-) where
  unfmap (Nat f) = Yoneda (f id)
