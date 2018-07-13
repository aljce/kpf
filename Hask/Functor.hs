{-|
Module      : Hask.Functor
Description : Functors and Categories
Copyright   : (c) Edward Kmett, 2018
                  Kyle McKean,  2018
License     : BSD-3-Clause
Maintainer  : mckean.kylej@gmail.com
Stability   : experimental
Portability : portatable

__FIXME__: Doc

@since 0.1.0
-}
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

module Hask.Functor 
  (
  -- * Categories
  -- $setup
    type Cat
  , type Op
  , Yoneda(..)
  , Always
  , Category(..)
  -- * Functors
  , type Hask
  , type OldFunctor
  , Functor(..)
  , FunctorOf
  , Nat(..)
  -- * Contravariant Functors
  , contramap
  -- * Bifunctors
  , BifunctorOf
  , first
  , second
  , bimap
  -- * Profunctors
  , lmap
  , rmap
  , dimap
  ) where

import qualified Prelude as Base hiding (id, (.))
import qualified Data.Bifunctor as Base
import qualified Data.Complex as Base
import qualified Control.Category as Base
import qualified Control.Monad.ST as Strict
import qualified Control.Monad.ST.Lazy as Lazy

import Data.Kind (Constraint, Type)
import Data.Type.Equality ((:~:)(..))
import qualified Data.Type.Equality as Equality
import Data.Type.Coercion (Coercion(..))
import qualified Data.Type.Coercion as Coercion

import Data.Constraint (Dict(..), (:-)(..), (\\), mapDict)
import qualified Data.Constraint as Constraint

-- $setup
-- >>> import Prelude (Ord(..))
-- >>> :set -XGADTs
-- >>> :set -XRankNTypes
-- >>> :set -XTypeFamilies
-- >>> :set -XTypeOperators
-- >>> :set -XTypeInType
--
-- The peano natural numbers lifted to the type level with '-XDataKinds':
--
-- >>> data Nat = Z | S Nat
--
-- A proof that 'n' is less than 'm':
--
-- >>> :{
-- data (n :: Nat) <= (m :: Nat) :: Type where
--   Zero :: Z <= m
--   Succ :: n <= m -> S n <= S m
-- :}

-- | This is the type of categories also known as the 
-- [Hom Functor](https:ncatlab.org/nlab/show/hom-functor).
-- Unlike standard category theory this Hom Functor is curried so:
--
-- \( Cat : C^{op} \to [ C, Set ] \)
--
-- >>> :kind ((->) :: Cat Type)
-- ((->) :: Cat Type) :: * -> * -> *
-- >>> :kind ((:-) :: Cat Constraint)
-- ((:-) :: Cat Constraint) :: Constraint -> Constraint -> *
-- >>> :kind ((<=) :: Cat Nat)
-- ((<=) :: Cat Nat) :: Nat -> Nat -> *
--
-- @since 0.1.0
type Cat i = i -> i -> Type

-- | The [Yoneda Embedding](https://ncatlab.org/nlab/show/Yoneda+embedding)
--
-- \( \text{Yoneda} : C \to [ C^{op}, Set ] \)
--
-- This type is a type level equivalent to 'flip' from the prelude.
--
-- @since 0.1.0
newtype Yoneda (p :: Cat i) :: Cat i where
  Yoneda 
    :: { runYoneda :: p b a 
       } 
    ->  Yoneda p a b

-- | The trivally true constraint. This constraint is satisfied regardless of
-- the chosen 'a'.
--
-- >>> Dict :: Dict (Always ())
-- Dict
-- >>> Dict :: forall a. Dict (Always a)
-- Dict
--
-- @since 0.1.0
class Always a where
instance Always a where

-- | The opositie category \(C^{op}\) from \(C\).
--
-- >>> :kind! Op (->)
-- Op (->) :: * -> * -> *
-- = Yoneda (->)
--
-- >>> :kind! Op (:~:)
-- Op (:~:) :: i -> i -> *
-- = (:~:)
--
-- @since 0.1.0
type family Op (p :: Cat i) :: Cat i where
  Op p = Dom p

-- | >>> :{
-- instance Category (->) where
--   type Ob (->) = Always
--   id = \x -> x
--   f . g = \x -> f (g x)
--   source _ = Dict
--   target _ = Dict
--   op = Yoneda
--   unop = runYoneda
-- :}
--
-- The arrow type (->) satisifes all the constraints for default signatures 
-- to kick in so the above instance can be written as:
--
-- >>> instance Category (->)
-- 
-- >>> :r
--
-- >>> :{
-- data OrdHask :: Cat Type where
--   OrdHask :: (Ord a, Ord b) => (a -> b) -> OrdHask a b
-- :}
--
-- >>> :{
-- instance Category OrdHask where
--   type Ob OrdHask = Ord
--   id = OrdHask id
--   OrdHask f . OrdHask g = OrdHask (f . g)
--   source OrdHask{} = Dict
--   target OrdHask{} = Dict
-- instance Functor (OrdHask a) where
--   type Dom (OrdHask a) = OrdHask
--   type Cod (OrdHask a) = (->)
--   fmap = (.)
-- instance Functor OrdHask where
--   type Dom OrdHask = Yoneda OrdHask
--   type Cod OrdHask = Nat OrdHask (->)
--   fmap (Yoneda f) = Nat (\g -> g . f)
-- :}
--
-- >>> import Data.Set (Set, map)
--
-- >>> :{
-- instance Functor Set where
--   type Dom Set = OrdHask
--   type Cod Set = (->)
--   fmap (OrdHask f) = map f
-- :}
--
-- @since 0.1.0


class (BifunctorOf (Op p) p (->) p, Ob (Op p) ~ Ob p) 
  => Category (p :: Cat i) where
  -- | This type family defaults to 'Always' as many common categories do not 
  -- need to constrain their objects.
  --
  -- @since 0.1.0
  type Ob p :: i -> Constraint
  type Ob p = Always

  -- | __FIXME__: Doc
  --
  -- @since 0.1.0
  id :: Ob p a => p a a
  default id :: (Ob p ~ Always, Base.Category p) => p a a 
  id = Base.id

  -- | __FIXME__: Doc
  --
  -- @since 0.1.0
  (.) :: p b c -> p a b -> p a c
  default (.) :: (Base.Category p) => p b c -> p a b -> p a c
  (.) = (Base..)
  
  -- | __FIXME__: Doc
  --
  -- @since 0.1.0
  source :: p a b -> Dict (Ob p a)
  default source :: (Ob p ~ Always) => p a b -> Dict (Ob p a)
  source _ = Dict

  -- | __FIXME__: Doc
  --
  -- @since 0.1.0
  target :: p a b -> Dict (Ob p b)
  default target :: (Ob p ~ Always) => p a b -> Dict (Ob p b)
  target _ = Dict

  -- | __FIXME__: Doc
  --
  -- @since 0.1.0
  op :: p b a -> Op p a b
  default op :: Op p ~ Yoneda p => p b a -> Op p a b
  op = Yoneda
  
  -- | __FIXME__: Doc
  --
  -- @since 0.1.0
  unop :: Op p b a -> p a b
  default unop :: Op p ~ Yoneda p => Op p b a -> p a b
  unop = runYoneda

-- | __FIXME__: Doc
--
-- @since 0.1.0
type family Hask :: Cat ob where
  Hask = ((->) :: Cat Type)

-- | __FIXME__: Doc
--
-- @since 0.1.0
type family OldFunctor (k :: Type) :: k -> Constraint where
  OldFunctor (Type -> Type) = Base.Functor
 
-- | __FIXME__: Doc
-- 
-- @since 0.1.0
class (Category (Dom f), Category (Cod f)) => Functor (f :: i -> j) where
  -- | __FIXME__: Doc
  --
  -- @since 0.1.0
  type Dom f :: Cat i
  type Dom f = Hask

  -- | __FIXME__: Doc
  --
  -- @since 0.1.0
  type Cod f :: Cat j
  type Cod f = Hask

  -- | __FIXME__: Doc
  --
  -- @since 0.1.0
  fmap :: Dom f a b -> Cod f (f a) (f b)
  default fmap 
    :: (i ~ Type, j ~ Type, Dom f ~ Hask, Cod f ~ Hask, OldFunctor (i -> j) f)  
    => Dom f a b -> Cod f (f a) (f b)
  fmap = Base.fmap

-- | __FIXME__: Doc
--
-- @since 0.1.0
class (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f | f -> p q
instance (Functor f, Dom f ~ p, Cod f ~ q) => FunctorOf p q f

-- | __FIXME__: Doc
--
-- @since 0.1.0
data Nat (p :: Cat i) (q :: Cat j) (f :: i -> j) (g :: i -> j) where
  Nat 
    :: (FunctorOf p q f, FunctorOf p q g)
    => { runNat :: forall a. Ob p a => q (f a) (g a)  -- ^ __FIXME__: Doc
       } 
    -> Nat p q f g

-- | __FIXME__: Doc
--
-- @since 0.1.0
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

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance (Category p, Category q) => Functor (Nat p q) where
  type Dom (Nat p q) = Yoneda (Nat p q)
  type Cod (Nat p q) = Nat (Nat p q) (->)
  fmap (Yoneda nat1) = Nat (\nat2 -> nat2 . nat1)

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance (Category p, Category q) => Functor (Nat p q f) where
  type Dom (Nat p q f) = Nat p q
  type Cod (Nat p q f) = (->)
  fmap = (.)

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Category (->) where

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor (->) where
  type Dom (->) = Yoneda (->)
  type Cod (->) = Nat (->) (->)
  fmap (Yoneda f1) = Nat (\f2 -> f2 . f1)

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance (Category p, Op p ~ Yoneda p) => Category (Yoneda p) where
  type Ob (Yoneda p) = Ob p
  id = Yoneda id
  Yoneda f . Yoneda g = Yoneda (g . f)
  source (Yoneda f) = target f
  target (Yoneda f) = source f
  unop = Yoneda
  op = runYoneda

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance (Category p, Op p ~ Yoneda p) => Functor (Yoneda p a) where
  type Dom (Yoneda p a) = Yoneda p
  type Cod (Yoneda p a) = (->)
  fmap = (.)

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance (Category p, Op p ~ Yoneda p) => Functor (Yoneda p) where
  type Dom (Yoneda p) = p
  type Cod (Yoneda p) = Nat (Yoneda p) (->)
  fmap f1 = Nat (\f2 -> f2 . Yoneda f1)

--------------------------------------------------------------------------------
-- Type Constraints
--------------------------------------------------------------------------------

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor Dict where
  type Dom Dict = (:-)
  type Cod Dict = (->)
  fmap = mapDict

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Category (:-) where
  id = Constraint.refl
  (.) = Constraint.trans

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor ((:-) e) where
  type Dom ((:-) e) = (:-)
  type Cod ((:-) e) = (->)
  fmap = (.)

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor (:-) where
  type Dom (:-) = Yoneda (:-)
  type Cod (:-) = Nat (:-) (->)
  fmap (Yoneda d1) = Nat (\d2 -> d2 . d1)

--------------------------------------------------------------------------------
-- * Common Functors
--------------------------------------------------------------------------------

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor ((->) e) where

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor ((,) e) where

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor (Base.Either e) where

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor [] where

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor Base.Maybe where

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor Base.IO where

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor Base.Complex where

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor (Strict.ST s) where

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor (Lazy.ST s) where

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor (,) where
  type Dom (,) = (->)
  type Cod (,) = Nat (->) (->)
  fmap f = Nat (\(a,b) -> (f a, b))

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor Base.Either where
  type Dom Base.Either = (->)
  type Cod Base.Either = Nat (->) (->)
  fmap f0 = Nat (Base.first f0) where

--------------------------------------------------------------------------------
-- * Type Equality
--------------------------------------------------------------------------------

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Category (:~:) where
  op = Equality.sym
  unop = Equality.sym

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor (:~:) where
  type Dom (:~:) = (:~:)
  type Cod (:~:) = Nat (:~:) (->)
  fmap f = Nat (. Equality.sym f)

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor ((:~:) e) where
  type Dom ((:~:) e) = (:~:)
  type Cod ((:~:) e) = (->)
  fmap = (.)

--------------------------------------------------------------------------------
-- * Type Coercions 
--------------------------------------------------------------------------------

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Category Coercion where
  op   = Coercion.sym
  unop = Coercion.sym

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor Coercion where
  type Dom Coercion = Coercion
  type Cod Coercion = Nat Coercion (->)
  fmap f = Nat (. Coercion.sym f)

-- | __FIXME__: Doc
--
-- @since 0.1.0
instance Functor (Coercion e) where
  type Dom (Coercion e) = Coercion
  type Cod (Coercion e) = (->)
  fmap = (.)

--------------------------------------------------------------------------------
-- * Contravariant Functors
--------------------------------------------------------------------------------

-- | __FIXME__: Doc
--
-- @since 0.1.0
contramap :: Functor f => Op (Dom f) a b -> Cod f (f b) (f a)
contramap = fmap . unop

--------------------------------------------------------------------------------
-- * Bi/Pro Functors
--------------------------------------------------------------------------------

-- | __FIXME__: Doc
--
-- @since 0.1.0
class (Functor f, Dom f ~ p, Cod f ~ Nat q r, Category p, Category q, Category r) =>
  BifunctorOf (p :: Cat i) (q :: Cat j) (r :: Cat k) (f :: i -> j -> k) | f -> p q r where
instance (Functor f, Dom f ~ p, Cod f ~ Nat q r, Category p, Category q, Category r) => 
  BifunctorOf p q r f where

-- | __FIXME__: Doc
--
-- @since 0.1.0
first :: (BifunctorOf p q r f, Ob q c) => p a b -> r (f a c) (f b c)
first p = runNat (fmap p)

-- | __FIXME__: Doc
--
-- @since 0.1.0
second :: forall p q r f a c d. (BifunctorOf p q r f, Ob p a) => q c d -> r (f a c) (f a d)
second q = fmap q \\ lemma
  where
    lemma :: Ob p a :- FunctorOf q r (f a)
    lemma = ob

-- | __FIXME__: Doc
--
-- @since 0.1.0
bimap :: BifunctorOf p q r f => p a b -> q c d -> r (f a c) (f b d)
bimap d p = case (source d, target p) of
  (Dict, Dict) -> first d . second p

-- | __FIXME__: Doc
--
-- @since 0.1.0
lmap :: (BifunctorOf p q r f, Ob q c) => Op p a b -> r (f b c) (f a c)
lmap = first . unop 

-- | __FIXME__: Doc
--
-- @since 0.1.0
rmap :: (BifunctorOf p q r f, Ob p a) => q c d -> r (f a c) (f a d)
rmap = second

-- | __FIXME__: Doc
--
-- @since 0.1.0
dimap :: BifunctorOf p q r f => Op p a b -> q c d -> r (f b c) (f a d)
dimap = bimap . unop


