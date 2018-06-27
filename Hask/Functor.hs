{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeInType #-}

module Hask.Functor where

import qualified Prelude as Base
import qualified Data.Bifunctor as Base
import qualified Data.Complex as Base
import qualified Control.Monad.ST as Strict
import qualified Control.Monad.ST.Lazy as Lazy

import Data.Kind (Constraint, Type)
import Data.Type.Equality ((:~:)(..))
import qualified Data.Type.Equality as Equality
import Data.Type.Coercion (Coercion(..))
import qualified Data.Type.Coercion as Coercion

import Data.Constraint (Dict(..), (:-)(..), (\\), mapDict)
import qualified Data.Constraint as Constraint

type Cat i = i -> i -> Type

newtype Yoneda p a b = Yoneda { runYoneda :: p b a }

class Always (p :: Cat i) (a :: i)
instance Always p a

class (Functor p, Dom p ~ Op p, Cod p ~ Nat p (->), Ob (Op p) ~ Ob p) => Category (p :: Cat i) where
  type Op p :: Cat i
  type Op p = Yoneda p

  type Ob p :: i -> Constraint
  type Ob p = Always p

  id :: Ob p a => p a a
  (.) :: p b c -> p a b -> p a c

  source :: p a b -> Dict (Ob p a)
  default source :: (Ob p ~ Always p) => p a b -> Dict (Ob p a)
  source _ = Dict

  target :: p a b -> Dict (Ob p b)
  default target :: (Ob p ~ Always p) => p a b -> Dict (Ob p b)
  target _ = Dict

  op :: p b a -> Op p a b
  default op :: Op p ~ Yoneda p => p b a -> Op p a b
  op = Yoneda
  
  unop :: Op p b a -> p a b
  default unop :: Op p ~ Yoneda p => Op p b a -> p a b
  unop = runYoneda

type family Hask :: Cat ob where
  Hask = ((->) :: Cat Type)

type family OldFunctor (k :: Type) :: k -> Constraint where
  OldFunctor (Type -> Type) = Base.Functor
 
class (Category (Dom f), Category (Cod f)) => Functor (f :: i -> j) where
  type Dom f :: Cat i
  type Dom f = Hask
  type Cod f :: Cat j
  type Cod f = Hask
  fmap :: Dom f a b -> Cod f (f a) (f b)
  default fmap :: (i ~ Type, j ~ Type, Dom f ~ Hask, Cod f ~ Hask, OldFunctor (i -> j) f) => Dom f a b -> Cod f (f a) (f b)
  fmap = Base.fmap

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
  type Dom (Nat p q) = Yoneda (Nat p q)
  type Cod (Nat p q) = Nat (Nat p q) (->)
  fmap (Yoneda nat1) = Nat (\nat2 -> nat2 . nat1)

instance (Category p, Category q) => Functor (Nat p q f) where
  type Dom (Nat p q f) = Nat p q
  type Cod (Nat p q f) = (->)
  fmap = (.)

instance Category (->) where
  id = Base.id
  (.) = (Base..)

instance Functor (->) where
  type Dom (->) = Yoneda (->)
  type Cod (->) = Nat (->) (->)
  fmap (Yoneda f1) = Nat (\f2 -> f2 . f1)

instance (Category p, Op p ~ Yoneda p) => Category (Yoneda p) where
  type Op (Yoneda p) = p
  type Ob (Yoneda p) = Ob p
  id = Yoneda id
  Yoneda f . Yoneda g = Yoneda (g . f)
  source (Yoneda f) = target f
  target (Yoneda f) = source f
  unop = Yoneda
  op = runYoneda

instance (Category p, Op p ~ Yoneda p) => Functor (Yoneda p a) where
  type Dom (Yoneda p a) = Yoneda p
  type Cod (Yoneda p a) = (->)
  fmap = (.)

instance (Category p, Op p ~ Yoneda p) => Functor (Yoneda p) where
  type Dom (Yoneda p) = p
  type Cod (Yoneda p) = Nat (Yoneda p) (->)
  fmap f1 = Nat (\f2 -> f2 . Yoneda f1)

--------------------------------------------------------------------------------
-- Type Constraints
--------------------------------------------------------------------------------

instance Functor Dict where
  type Dom Dict = (:-)
  type Cod Dict = (->)
  fmap = mapDict

instance Category (:-) where
  id = Constraint.refl
  (.) = Constraint.trans

instance Functor ((:-) e) where
  type Dom ((:-) e) = (:-)
  type Cod ((:-) e) = (->)
  fmap = (.)

instance Functor (:-) where
  type Dom (:-) = Yoneda (:-)
  type Cod (:-) = Nat (:-) (->)
  fmap (Yoneda d1) = Nat (\d2 -> d2 . d1)

--------------------------------------------------------------------------------
-- * Common Functors
--------------------------------------------------------------------------------

instance Functor ((->) e) where
instance Functor ((,) e) where
instance Functor (Base.Either e) where
instance Functor [] where
instance Functor Base.Maybe where
instance Functor Base.IO where
instance Functor Base.Complex where
instance Functor (Strict.ST s) where
instance Functor (Lazy.ST s) where

instance Functor (,) where
  type Dom (,) = (->)
  type Cod (,) = Nat (->) (->)
  fmap f = Nat (\(a,b) -> (f a, b))

instance Functor Base.Either where
  type Dom Base.Either = (->)
  type Cod Base.Either = Nat (->) (->)
  fmap f0 = Nat (Base.first f0) where

--------------------------------------------------------------------------------
-- * Type Equality
--------------------------------------------------------------------------------

instance Category (:~:) where
  type Op (:~:) = (:~:)
  id = Refl
  (.) = Base.flip Equality.trans
  op = Equality.sym
  unop = Equality.sym

instance Functor (:~:) where
  type Dom (:~:) = (:~:)
  type Cod (:~:) = Nat (:~:) (->)
  fmap f = Nat (. Equality.sym f)

instance Functor ((:~:) e) where
  type Dom ((:~:) e) = (:~:)
  type Cod ((:~:) e) = (->)
  fmap = (.)

--------------------------------------------------------------------------------
-- * Type Coercions 
--------------------------------------------------------------------------------

instance Category Coercion where
  type Op Coercion = Coercion
  id = Coercion
  (.) = Base.flip Coercion.trans
  op   = Coercion.sym
  unop = Coercion.sym

instance Functor Coercion where
  type Dom Coercion = Coercion
  type Cod Coercion = Nat Coercion (->)
  fmap f = Nat (. Coercion.sym f)

instance Functor (Coercion e) where
  type Dom (Coercion e) = Coercion
  type Cod (Coercion e) = (->)
  fmap = (.)

--------------------------------------------------------------------------------
-- * Contravariant Functors
--------------------------------------------------------------------------------

contramap :: Functor f => Op (Dom f) b a -> Cod f (f a) (f b)
contramap = fmap . unop
