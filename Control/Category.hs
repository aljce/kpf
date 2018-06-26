{-# language KindSignatures #-}
{-# language PolyKinds #-}
{-# language DataKinds #-}
{-# language TypeFamilies #-}
{-# language RankNTypes #-}
{-# language NoImplicitPrelude #-}
{-# language FlexibleContexts #-}
{-# language MultiParamTypeClasses #-}
{-# language EmptyDataDecls #-}
{-# language InstanceSigs #-}
{-# language GADTs #-}
{-# language ConstraintKinds #-}
{-# language FlexibleInstances #-}
{-# language TypeOperators #-}
{-# language ScopedTypeVariables #-}
{-# language DefaultSignatures #-}
{-# language FunctionalDependencies #-}
{-# language UndecidableSuperClasses #-}
{-# language UndecidableInstances #-}
{-# language TypeApplications #-}
{-# language TypeInType #-}

module Control.Category where

import qualified Prelude
import Prelude (Either(..), Maybe, IO)

import Data.Kind (Constraint, Type)
import qualified Data.Type.Coercion as Coercion
import Data.Type.Coercion (Coercion(..))
import qualified Data.Type.Equality as Equality
import Data.Type.Equality ((:~:)(..))

import Data.Constraint (Dict(..), (:-)(..), (\\))

import Unsafe.Coerce (unsafeCoerce)

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
  OldFunctor (Type -> Type) = Prelude.Functor
 
class (Category (Dom f), Category (Cod f)) => Functor (f :: i -> j) where
  type Dom f :: Cat i
  type Dom f = Hask
  type Cod f :: Cat j
  type Cod f = Hask
  fmap :: Dom f a b -> Cod f (f a) (f b)
  default fmap :: (i ~ Type, j ~ Type, Dom f ~ Hask, Cod f ~ Hask, OldFunctor (i -> j) f) => Dom f a b -> Cod f (f a) (f b)
  fmap = Prelude.fmap

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
  fmap (Yoneda f) = Nat (. f)

instance (Category p, Category q) => Functor (Nat p q f) where
  type Dom (Nat p q f) = Nat p q
  type Cod (Nat p q f) = (->)
  fmap = (.)

contramap :: Functor f => Op (Dom f) b a -> Cod f (f a) (f b)
contramap = fmap . unop

instance Category (->) where
  id = Prelude.id
  (.) = (Prelude..)

instance Functor (->) where
  type Dom (->) = Yoneda (->)
  type Cod (->) = Nat (->) (->)
  fmap (Yoneda f) = Nat (. f)

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
  fmap f = Nat (. Yoneda f)

--------------------------------------------------------------------------------
-- Type Constraints
--------------------------------------------------------------------------------

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
  type Dom (:-) = Yoneda (:-)
  type Cod (:-) = Nat (:-) (->)
  fmap (Yoneda f) = Nat (. f)

--------------------------------------------------------------------------------
-- * Common Functors
--------------------------------------------------------------------------------

instance Functor ((->) e) where
instance Functor ((,) e) where
instance Functor (Either e) where
instance Functor [] where
instance Functor Prelude.Maybe where
instance Functor IO where

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

--------------------------------------------------------------------------------
-- * Product Category
--------------------------------------------------------------------------------
type family Fst (a :: (i, j)) :: i where
  Fst '(x, y) = x

type family Snd (a :: (i, j)) :: j where
  Snd '(x, y) = y

data Product (p :: Cat i) (q :: Cat j) :: Cat (i, j) where
  Product :: p a c -> q b d -> Product p q '(a, b) '(c, d)

tupleEta :: forall (i :: Type) (j :: Type) (a :: (i, j)). a :~: '(Fst a, Snd a)
tupleEta = unsafeCoerce Refl

class (p (Fst a), q (Snd a)) => And (p :: i -> Constraint) (q :: j -> Constraint) (a :: (i, j)) where
instance (p (Fst a), q (Snd a)) => And p q a where 

instance (Category p, Category q) => Category (Product p q) where
  type Ob (Product p q) = And (Ob p) (Ob q)
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

--------------------------------------------------------------------------------
-- * Coproduct Category
--------------------------------------------------------------------------------

data Coproduct (p :: Cat i) (q :: Cat j) :: Cat (Either i j) where
  InjL :: p a c -> Coproduct p q (Left a)  (Left c)
  InjR :: q b d -> Coproduct p q (Right b) (Right d)
