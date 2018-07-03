{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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

import qualified Prelude as Base
import Data.Kind (Type, Constraint)

import Data.Constraint (Dict(..), (:-)(..))

import Hask.Functor
import Hask.Iso

data family Any :: k

data COMPOSE = Compose
type Compose = (Any 'Compose :: Cat i -> Cat j -> Cat k -> (j -> k) -> (i -> j) -> (i -> k))

newtype instance Any 'Compose p q r (f :: i -> Type) g a 
  = Comp { runComp :: f (g a) }

data instance Any 'Compose p q r (f :: i -> Constraint) g a where
  CompDict :: f (g a) => Any 'Compose p q r f g a

class Category r => Composed (r :: Cat k) where
  _Compose 
    :: (FunctorOf p q g, FunctorOf p q i, FunctorOf q r f, FunctorOf q r h) 
    => Iso r r (->) (Compose p q r f g a) (Compose p q r h i b) (f (g a)) (h (i b))

instance Composed (->) where
  _Compose = dimap runComp Comp

instance Composed (:-) where
  _Compose 
    :: forall p q f h g i a b
    .  (FunctorOf p q g, FunctorOf p q i, FunctorOf q (:-) f, FunctorOf q (:-) h) 
    => Iso (:-) (:-) (->) (Compose p q (:-) f g a) (Compose p q (:-) h i b) (f (g a)) (h (i b))
  _Compose = dimap hither yon
    where
      hither :: void
      hither = Base.undefined
      yon :: h (i b) :- Compose p q (:-) h i b
      yon = Base.undefined



instance (Category p, Category q, Composed r, FunctorOf q r f, FunctorOf p q g) => Functor (Compose p q r f g) where
  type Dom (Compose p q r f g) = p
  type Cod (Compose p q r f g) = r
  fmap = _Compose . fmap . fmap
