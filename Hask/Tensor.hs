{-|
Module      : Hask.Tensor
Description : Associative Bifunctors
Copyright   : (c) Edward Kmett, 2018
                  Kyle McKean,  2018
License     : BSD-3-Clause
Maintainer  : mckean.kylej@gmail.com
Stability   : experimental
Portability : portable

__FIXME__: Doc
-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE UndecidableSuperClasses #-}
module Hask.Tensor where

import Prelude (Either(..))
import qualified Prelude as Base ()

import Data.Void (Void)

import Hask.Functor
import Hask.Iso

-- | __FIXME__: Doc
class BifunctorOf p p p f => Semitensor (p :: Cat i) (f :: i -> i -> i) | f -> p where
  -- | __FIXME__: Doc
  associate 
    :: (Ob p a, Ob p b, Ob p c, Ob p x, Ob p y, Ob p z) 
    => Iso p p (->) (f (f a b) c) (f (f x y) z) (f a (f b c)) (f x (f y z))

instance Semitensor (->) Either where
  associate = dimap hither yon
    where
      hither :: Either (Either a b) c -> Either a (Either b c)
      hither = \case
        Left (Left a)  -> Left a
        Left (Right b) -> Right (Left b)
        Right c        -> Right (Right c)
      yon :: Either x (Either y z) -> Either (Either x y) z
      yon = \case
        Left x          -> Left (Left x)
        Right (Left y)  -> Left (Right y)
        Right (Right z) -> Right z

instance Semitensor (->) (,) where
  associate = dimap hither yon
    where
      hither :: ((a, b), c) -> (a, (b, c))
      hither ((a, b), c) = (a, (b, c))
      yon :: (x, (y, z)) -> ((x, y), z)
      yon (x, (y, z)) = ((x, y), z)

-- | __FIXME__: Doc
class Semitensor p f => Tensor p (f :: i -> i -> i) where
  -- | __FIXME__: Doc
  type I f :: i
  -- | __FIXME__: Doc
  lambda :: (Ob p a, Ob p b) => Iso p p (->) (f (I f) a) (f (I f) b) a b
  -- | __FIXME__: Doc
  rho    :: (Ob p a, Ob p b) => Iso p p (->) (f a (I f)) (f b (I f)) a b

instance Tensor (->) Either where
  type I Either = Void
  lambda = dimap (\(Right a) -> a) Right
  rho = dimap (\(Left a) -> a) Left

instance Tensor (->) (,) where
  type I (,) = ()
  lambda = dimap (\((), a) -> a) (\b -> ((), b))
  rho = dimap (\(a, ()) -> a) (\b -> (b, ()))
