{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
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

module Hask.Functor.Polynomial 
  (
  -- * 0 Category
    Empty
  , empty
  , Vacuous
  -- * 1 Category
  , Unit(..)
  -- * Product Category
  , Product(..)
  , ProductOb
  , type Fst
  , type Snd
  -- * Coproduct Category
  , Coproduct(..)
  , coproduct
  , CoproductOb(..)
  ) where

import Prelude (type Either(..))

import Data.Kind (Constraint, Type)
import Data.Type.Equality ((:~:)(..))
import Data.Void (type Void)

import Unsafe.Coerce (unsafeCoerce)

import Data.Constraint (Dict(..), Bottom(..))

import Hask.Functor
import Hask.Functor.Faithful
import Hask.Groupoid

--------------------------------------------------------------------------------
-- * 0 Category
--------------------------------------------------------------------------------

data Empty :: Cat Void where

empty :: Empty a b -> void
empty = \case{}

class Bottom => Vacuous a where

instance Category Empty where
  type Ob Empty = Vacuous
  id = no
  e . _ = empty e
  source = empty
  target = empty

instance Functor Empty where
  type Dom Empty = Yoneda Empty
  type Cod Empty = Nat Empty (->)
  fmap = empty . runYoneda

instance Functor (Empty a) where
  type Dom (Empty a) = Empty
  type Cod (Empty a) = (->)
  fmap = empty

instance Groupoid Empty where
  sym = empty

--------------------------------------------------------------------------------
-- * 1 Category
--------------------------------------------------------------------------------

data Unit :: Cat () where
  Unit :: Unit a b

instance Category Unit where
  id = Unit
  _ . _ = Unit

instance Functor Unit where
  type Dom Unit = Yoneda Unit
  type Cod Unit = Nat Unit (->)
  fmap _ = Nat (\_ -> Unit)

instance Functor (Unit a) where
  type Dom (Unit a) = Unit
  type Cod (Unit a) = (->)
  fmap = (.)

instance Groupoid Unit where
  sym _ = Unit

instance FullyFaithful Unit where
  unfmap _ = Yoneda Unit

instance FullyFaithful (Unit a) where
  unfmap _ = Unit

--------------------------------------------------------------------------------
-- * Product Category
--------------------------------------------------------------------------------

type family Fst (a :: (i, j)) :: i where
  Fst '(x, y) = x

type family Snd (a :: (i, j)) :: j where
  Snd '(x, y) = y

data Product (p :: Cat i) (q :: Cat j) :: Cat (i, j) where
  Product 
    :: { proj1 :: p a c
       , proj2 :: q b d } -> Product p q '(a, b) '(c, d)

tupleEta :: forall (i :: Type) (j :: Type) (a :: (i, j)). a :~: '(Fst a, Snd a)
tupleEta = unsafeCoerce Refl

class (p (Fst a), q (Snd a)) => ProductOb (p :: i -> Constraint) (q :: j -> Constraint) (a :: (i, j)) where
instance (p (Fst a), q (Snd a)) => ProductOb p q a where 

instance (Category p, Category q) => Category (Product p q) where
  type Ob (Product p q) = ProductOb (Ob p) (Ob q)
  id :: forall a. Ob (Product p q) a => Product p q a a
  id = case tupleEta @_ @_ @a of
    Refl -> Product id id
  Product p1 q1 . Product p2 q2 = Product (p1 . p2) (q1 . q2)
  source (Product p q) = case (source p, source q) of
    (Dict, Dict) -> Dict
  target (Product p q) = case (target p, target q) of
    (Dict, Dict) -> Dict

instance (Category p, Category q) => Functor (Product p q) where
  type Dom (Product p q) = Yoneda (Product p q)
  type Cod (Product p q) = Nat (Product p q) (->)
  fmap (Yoneda prod1) = Nat (\prod2 -> prod2 . prod1)

instance (Category p, Category q) => Functor (Product p q a) where
  type Dom (Product p q a) = Product p q
  type Cod (Product p q a) = (->)
  fmap = (.)

instance (Groupoid p, Groupoid q) => Groupoid (Product p q) where
  sym (Product p q) = Product (sym p) (sym q)

--------------------------------------------------------------------------------
-- * Coproduct Category
--------------------------------------------------------------------------------

data Coproduct (p :: Cat i) (q :: Cat j) :: Cat (Either i j) where
  InjL :: p a c -> Coproduct p q (Left a)  (Left c)
  InjR :: q b d -> Coproduct p q (Right b) (Right d)

coproduct
  :: (forall a c. (Left  a ~ x, Left  c ~ y) => p a c -> r)
  -> (forall b d. (Right b ~ x, Right d ~ y) => q b d -> r)
  -> Coproduct p q x y
  -> r
coproduct f g = \case
  InjL p -> f p
  InjR q -> g q

class CoproductOb (p :: i -> Constraint) (q :: j -> Constraint) (a :: Either i j) where
  coproductOb :: (forall x. (a ~ Left x, p x) => r) -> (forall y. (a ~ Right y, q y) => r) -> r
instance p x => CoproductOb p q (Left x)  where
  coproductOb f _ = f
instance q y => CoproductOb p q (Right y) where
  coproductOb _ g = g

instance (Category p, Category q) => Category (Coproduct p q) where
  type Ob (Coproduct p q) = CoproductOb (Ob p) (Ob q)
  id :: forall a. Ob (Coproduct p q) a => Coproduct p q a a
  id = coproductOb @_ @_ @(Ob p) @(Ob q) @a (InjL id) (InjR id)
  InjL p . InjL q = InjL (p . q)
  InjR p . InjR q = InjR (p . q)
  source (InjL p) = case source p of
    Dict -> Dict
  source (InjR q) = case source q of
    Dict -> Dict
  target (InjL p) = case target p of
    Dict -> Dict
  target (InjR q) = case target q of
    Dict -> Dict

instance (Category p, Category q) => Functor (Coproduct p q) where
  type Dom (Coproduct p q) = Yoneda (Coproduct p q)
  type Cod (Coproduct p q) = Nat (Coproduct p q) (->)
  fmap (Yoneda coprod1) = Nat (\coprod2 -> coprod2 . coprod1)

instance (Category p, Category q) => Functor (Coproduct p q a) where
  type Dom (Coproduct p q a) = Coproduct p q
  type Cod (Coproduct p q a) = (->)
  fmap = (.)

instance (Groupoid p, Groupoid q) => Groupoid (Coproduct p q) where
  sym (InjL p) = InjL (sym p)
  sym (InjR q) = InjR (sym q)
