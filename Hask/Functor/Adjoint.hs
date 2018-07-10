{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=2 #-}
module Hask.Functor.Adjoint where

import qualified Prelude as Base

import Unsafe.Coerce (unsafeCoerce)

import Hask.Functor
import Hask.Functor.Polynomial
import Hask.Functor.Compose
import Hask.Iso

class (Functor f, Functor g, Dom f ~ Cod g) => (f :: j -> i) -| (g :: i -> j) | f -> g, g -> f where
  adjoint :: Iso (->) (->) (->) (Cod f (f a) b) (Cod f (f c) d) (Cod g a (g b)) (Cod g c (g d))

instance (,) e -| (->) e where
  adjoint = dimap (\f a e -> f (e, a)) (\f (e, c) -> f c e)

data DIAGONAL = Diagonal
type Diagonal = (Any 'Diagonal :: Cat i -> i -> (i, i))

class Category p => Diagonals (p :: Cat i) where
  _Diagonal :: Iso (Product p p) (Product p p) (->) (Diagonal p a) (Diagonal p b) ('(a, a)) ('(b, b))

instance Diagonals (->) where
  _Diagonal = unsafeCoerce

instance Diagonals p => Functor (Diagonal p) where
  type Dom (Diagonal p) = p
  type Cod (Diagonal p) = Product p p
  fmap p = _Diagonal (Product p p)

data PROD = Prod
type Prod = (Any 'Prod :: Cat i -> (i, i) -> i)

class (Category p, BifunctorOf p p p (Times p)) => Prods (p :: Cat i) where
  type Times (p :: Cat i) :: i -> i -> i
  _Prod :: Iso p p (->) (Prod p '(a, b)) (Prod p '(c, d)) (Times p a b) (Times p c d)

instance Prods (->) where
  type Times (->) = (,)
  _Prod = unsafeCoerce

instance Prods p => Functor (Prod p) where
  type Dom (Prod p) = Product p p
  type Cod (Prod p) = p
  fmap (Product p q) = _Prod (bimap p q)

instance (Diagonals p, Prods p) => Diagonal p -| Prod p where
  adjoint = dimap Base.undefined Base.undefined
