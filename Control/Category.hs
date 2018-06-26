{-# language KindSignatures #-}
{-# language PolyKinds #-}
{-# language DataKinds #-}
{-# language TypeFamilies #-}
{-# language RankNTypes #-}
{-# language NoImplicitPrelude #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language GADTs #-}
{-# language ConstraintKinds #-}
{-# language FlexibleInstances #-}
{-# language TypeOperators #-}
{-# language ScopedTypeVariables #-}
{-# language DefaultSignatures #-}
{-# language FunctionalDependencies #-}
{-# language UndecidableSuperClasses #-}
{-# language UndecidableInstances #-}
{-# language TypeInType #-}

module Control.Category where

import qualified Data.Type.Coercion as Coercion
import Data.Type.Coercion (Coercion(..))
import qualified Data.Type.Equality as Equality
import Data.Type.Equality ((:~:)(..))
import Data.Kind (Constraint, Type)
import qualified Prelude
import Prelude (Either(..), Maybe, IO)

type Cat i = i -> i -> Type

newtype Y p a b = Y { getY :: p b a }

class Vacuous (p :: Cat i) (a :: i)
instance Vacuous p a

data Dict (p :: Constraint) where
  Dict :: p => Dict p

class (Functor p, Dom p ~ Op p, Cod p ~ Nat p (->), Ob (Op p) ~ Ob p) => Category (p :: Cat i) where
  type Op p :: Cat i
  type Op p = Y p

  type Ob p :: i -> Constraint
  type Ob p = Vacuous p

  id :: Ob p a => p a a
  (.) :: p b c -> p a b -> p a c

  source :: p a b -> Dict (Ob p a)
  default source :: (Ob p ~ Vacuous p) => p a b -> Dict (Ob p a)
  source _ = Dict

  target :: p a b -> Dict (Ob p b)
  default target :: (Ob p ~ Vacuous p) => p a b -> Dict (Ob p b)
  target _ = Dict

  op :: p b a -> Op p a b
  default op :: Op p ~ Y p => p b a -> Op p a b
  op = Y
  
  unop :: Op p b a -> p a b
  default unop :: Op p ~ Y p => Op p b a -> p a b
  unop = getY

type family Hask :: Cat ob where
  Hask = ((->) :: Cat Type)

class (Category (Dom f), Category (Cod f)) => Functor (f :: i -> j) where
  type Dom f :: Cat i
  type Dom f = Hask
  type Cod f :: Cat j
  type Cod f = Hask
  fmap :: Dom f a b -> Cod f (f a) (f b)
  {- default fmap :: (i ~ Type, j ~ Type, Dom f ~ Hask, Cod f ~ Hask) => Dom f a b -> Cod f (f a) (f b) -}
  {- fmap = _ -}

class (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f | f -> p q
instance (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f

data Nat (p :: Cat i) (q :: Cat j) (f :: i -> j) (g :: i -> j) where
  Nat :: (FunctorOf p q f, FunctorOf p q g) => { runNat :: forall a. Ob p a => q (f a) (g a) } -> Nat p q f g

instance (Category p, Category q) => Category (Nat p q) where
  type Ob (Nat p q) = FunctorOf p q
  id = Nat id1 where
    id1 :: forall f x. (FunctorOf p q f, Ob p x) => q (f x) (f x)
    id1 = id \\ (ob :: Ob p x :- Ob q (f x))
  Nat f . Nat g = Nat (f . g)
  source Nat{} = Dict
  target Nat{} = Dict

ob :: forall p q f a. FunctorOf p q f => Ob p a :- Ob q (f a)
ob = Sub (case source (fmap id :: q (f a) (f a)) of Dict -> Dict)

instance (Category p, Category q) => Functor (Nat p q) where
  type Dom (Nat p q) = Y (Nat p q)
  type Cod (Nat p q) = Nat (Nat p q) (->)
  fmap (Y f) = Nat (. f)

instance (Category p, Category q) => Functor (Nat p q f) where
  type Dom (Nat p q f) = Nat p q
  type Cod (Nat p q f) = (->)
  fmap = (.)

contramap :: Functor f => Op (Dom f) b a -> Cod f (f a) (f b)
contramap = fmap . unop

instance Category (->) where
  id = Prelude.id
  (.) = (Prelude..)

instance Functor ((->) e) where
  type Dom ((->) e) = (->)
  type Cod ((->) e) = (->)
  fmap = (.)

instance Functor (->) where
  type Dom (->) = Y (->)
  type Cod (->) = Nat (->) (->)
  fmap (Y f) = Nat (. f)

instance (Category p, Op p ~ Y p) => Category (Y p) where
  type Op (Y p) = p
  type Ob (Y p) = Ob p
  id = Y id
  Y f . Y g = Y (g . f)
  source (Y f) = target f
  target (Y f) = source f
  unop = Y
  op = getY

instance (Category p, Op p ~ Y p) => Functor (Y p a) where
  type Dom (Y p a) = Y p
  type Cod (Y p a) = (->)
  fmap = (.)

instance (Category p, Op p ~ Y p) => Functor (Y p) where
  type Dom (Y p) = p
  type Cod (Y p) = Nat (Y p) (->)
  fmap f = Nat (. Y f)

--------------------------------------------------------------------------------
-- Type Constraints
--------------------------------------------------------------------------------

infixl 1 \\ -- comment required for cpp
(\\) :: a => (b => r) -> (a :- b) -> r
r \\ Sub Dict = r

newtype p :- q = Sub (p => Dict q)

instance Functor Dict where
  type Dom Dict = (:-)
  type Cod Dict = (->)
  fmap p Dict = case p of
    Sub q -> q

instance Category (:-) where
  id = Sub Dict
  f . g = Sub (Dict \\ f \\ g)

instance Functor ((:-) e) where
  type Dom ((:-) e) = (:-)
  type Cod ((:-) e) = (->)
  fmap = (.)

instance Functor (:-) where
  type Dom (:-) = Y (:-)
  type Cod (:-) = Nat (:-) (->)
  fmap (Y f) = Nat (. f)

--------------------------------------------------------------------------------
-- * Common Functors
--------------------------------------------------------------------------------

instance Functor ((,) e) where
  type Dom ((,) e) = (->)
  type Cod ((,) e) = (->)
  fmap f ~(a,b) = (a, f b)

instance Functor (Either e) where
  type Dom (Either e) = (->)
  type Cod (Either e) = (->)
  fmap _ (Left a) = Left a
  fmap f (Right b) = Right (f b)

instance Functor [] where
  type Dom [] = (->)
  type Cod [] = (->)
  fmap = Prelude.fmap

instance Functor Prelude.Maybe where
  type Dom Maybe = (->)
  type Cod Maybe = (->)
  fmap = Prelude.fmap

instance Functor IO where
  type Dom IO = (->)
  type Cod IO = (->)
  fmap = Prelude.fmap

instance Functor (,) where
  type Dom (,) = (->)
  type Cod (,) = Nat (->) (->)
  fmap f = Nat (\(a,b) -> (f a, b))

instance Functor Either where
  type Dom Either = (->)
  type Cod Either = Nat (->) (->)
  fmap f0 = Nat (go f0) where
    go :: (a -> b) -> Either a c -> Either b c
    go f (Left a)  = Left (f a)
    go _ (Right b) = Right b

--------------------------------------------------------------------------------
-- * Groupoids
--------------------------------------------------------------------------------

class Category p => Groupoid p where
  sym :: p a b -> p b a

instance (Category p, Groupoid q) => Groupoid (Nat p q) where
  sym f@Nat{} = Nat (sym (runNat f))

--------------------------------------------------------------------------------
-- * Type Equality
--------------------------------------------------------------------------------

instance Category (:~:) where
  type Op (:~:) = (:~:)
  id = Refl
  (.) = Prelude.flip Equality.trans
  op = sym
  unop = sym

instance Functor (:~:) where
  type Dom (:~:) = (:~:)
  type Cod (:~:) = Nat (:~:) (->)
  fmap f = Nat (. Equality.sym f)

instance Functor ((:~:) e) where
  type Dom ((:~:) e) = (:~:)
  type Cod ((:~:) e) = (->)
  fmap = (.)

instance Groupoid (:~:) where
  sym = Equality.sym

--------------------------------------------------------------------------------
-- * Type Coercions 
--------------------------------------------------------------------------------

instance Category Coercion where
  type Op Coercion = Coercion
  id = Coercion
  (.) = Prelude.flip Coercion.trans
  op   = sym
  unop = sym

instance Functor Coercion where
  type Dom Coercion = Coercion
  type Cod Coercion = Nat Coercion (->)
  fmap f = Nat (. Coercion.sym f)

instance Functor (Coercion e) where
  type Dom (Coercion e) = Coercion
  type Cod (Coercion e) = (->)
  fmap = (.)

instance Groupoid Coercion where
  sym = Coercion.sym
