{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Hask.Iso
  (
  -- * Isomorphisms
    type Iso
  -- * Yoneda's Lemma
  , yoneda
  ) where

import qualified Prelude as Base ()

import Hask.Functor

--------------------------------------------------------------------------------
-- * Isomorphisms
--------------------------------------------------------------------------------

type Iso c d e s t a b = forall f. BifunctorOf (Op c) d e f => f a b -> f s t

--------------------------------------------------------------------------------
-- * Yonedas lemma
--------------------------------------------------------------------------------

yoneda 
  :: forall p f g a b
  .  (Ob p a, FunctorOf p (->) g, FunctorOf p (->) (p b)) 
  => Iso (->) (->) (->) (Nat p (->) (p a) f) (Nat p (->) (p b) g) (f a) (g b)
yoneda = dimap hither yon
  where
    hither :: Nat p (->) (p a) f -> f a
    hither (Nat f) = f id
    yon :: g b -> Nat p (->) (p b) g 
    yon g = Nat (\p -> fmap p g)