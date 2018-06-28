{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE TypeInType #-}
module Hask.Functor.Faithful where

import qualified Prelude ()

import Data.Constraint (Dict, (:-), unmapDict)

import Hask.Functor

class Functor f => FullyFaithful (f :: i -> j) where
  unfmap :: Cod f (f a) (f b) -> Dom f a b

instance FullyFaithful Dict where
  unfmap = unmapDict

instance FullyFaithful (->) where
  unfmap (Nat f) = Yoneda (f id)

instance FullyFaithful (:-) where
  unfmap (Nat f) = Yoneda (f id)
