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

{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fconstraint-solver-iterations=2 #-}
module Hask.Functor.Adjoint where

import qualified Prelude as Base ()
import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..))

import Unsafe.Coerce (unsafeCoerce)

import Data.Constraint (Dict(..))

import Hask.Functor
import Hask.Functor.Polynomial
import Hask.Functor.Compose
import Hask.Iso

class (Functor f, Functor g, Dom f ~ Cod g) => (f :: j -> i) -| (g :: i -> j) | f -> g, g -> f where
  adjoint 
    -- TODO: These constraints are not needed but make the product instance possible
    -- We should remove them.
    :: (Ob (Dom f) a, Ob (Cod f) b, Ob (Cod g) c, Ob (Dom g) d)
    => Iso (->) (->) (->) (Cod f (f a) b) (Cod f (f c) d) (Cod g a (g b)) (Cod g c (g d))

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

class Category p => Prods (p :: Cat i) where
  fst  :: p (Prod p '(a, b)) a
  snd  :: p (Prod p '(a, b)) b
  pair :: p x a -> p x b -> p x (Prod p '(a, b))
 
data instance Any 'Prod (->) :: (Type, Type) -> Type where
  Times :: !a -> !b -> Prod (->) '(a, b)

instance Prods (->) where
  fst (Times a _) = a
  snd (Times _ b) = b
  pair f g x = Times (f x) (g x)

instance Prods p => Functor (Prod p) where
  type Dom (Prod p) = Product p p
  type Cod (Prod p) = p
  fmap (Product p q) = pair (p . fst) (q . snd)

instance (Diagonals p, Prods p) => Diagonal p -| Prod p where
  adjoint = dimap hither yon
    where
      hither :: forall a b. Ob p a => Product p p (Diagonal p a) b -> p a (Prod p b)
      hither p = case p . from _Diagonal of
        Product f g -> pair f g
      yon :: forall c d. p c (Prod p d) -> Product p p (Diagonal p c) d
      yon p = case tupleEta @_ @_ @d of
        Refl -> case source p of
          Dict -> Product (fst . p) (snd . p) . to _Diagonal
