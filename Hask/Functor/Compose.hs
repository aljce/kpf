{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=2 #-}
module Hask.Functor.Compose where

import qualified Prelude as Base ()
import Data.Kind (Type)

import Data.Constraint ((:-), Class(..), (:=>)(..))
import Data.Constraint.Unsafe (unsafeCoerceConstraint)

import Hask.Functor
import Hask.Iso

data family Any :: k

data COMPOSE = Compose
type Compose = (Any 'Compose :: Cat i -> Cat j -> Cat k -> (j -> k) -> (i -> j) -> (i -> k))

newtype instance Any 'Compose p q r (f :: i -> Type) g a 
  = Comp { runComp :: f (g a) }

class Category r => Composed (r :: Cat k) where
  _Compose 
    :: (FunctorOf p q g, FunctorOf p q i, FunctorOf q r f, FunctorOf q r h) 
    => Iso r r (->) (Compose p q r f g a) (Compose p q r h i b) (f (g a)) (h (i b))

instance Composed (->) where
  _Compose = dimap runComp Comp

-- TODO: Is there a way to do this without unsafeCoerceConstraint?
instance (Category p, Category q, Category r) => Class (f (g a)) (Compose p q r f g a) where
  cls = unsafeCoerceConstraint

instance (Category p, Category q, Category r) => f (g a) :=> Compose p q r f g a where
  ins = unsafeCoerceConstraint

instance Composed (:-) where
  _Compose = dimap cls ins

{- instance (Category x, Composed y) => Composed (Nat x y) where -}
  {- _Compose = dimap from to -}
    {- where -}
      {- from :: Nat x y (Compose p q (Nat x y) f g a) (f (g a)) -}
      {- from = Nat Base.undefined -}
      {- to :: Nat x y (h (i b)) (Compose p q (Nat x y) h i b) -}
      {- to = Nat Base.undefined -}

instance (Category p, Category q, Composed r, FunctorOf q r f, FunctorOf p q g) => Functor (Compose p q r f g) where
  type Dom (Compose p q r f g) = p
  type Cod (Compose p q r f g) = r
  fmap = _Compose . fmap . fmap

{- instance (Category p, Category q, Composed r, FunctorOf q r f) => Functor (Compose p q r f) where -}
  {- type Dom (Compose p q r f) = Nat p q -}
  {- type Cod (Compose p q r f) = Nat p r -}
  {- fmap (Nat f) = Nat Base.undefined -}
{-  -}
{- instance (Category p, Category q, Composed r) => Functor (Compose p q r) where -}
  {- type Dom (Compose p q r) = Nat q r -}
  {- type Cod (Compose p q r) = Nat (Nat p q) (Nat p r) -}
  {- fmap (Nat f) = Nat Base.undefined -}
