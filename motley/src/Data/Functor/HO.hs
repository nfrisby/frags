{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Functor.HO (
  -- *
  Applicative(..),
  Foldable(..),
  Functor(..),
  Traversable(..),
  -- *
  ToMaybe(..),
  -- *
  fromSingleton,
  toSingleton,
  Singleton(..),
  ) where

import qualified Control.Applicative as Applicative
import Control.Lens (view)
import qualified Control.Lens.Iso as Iso
import Data.Kind (Constraint)
import Data.Maybe (Maybe) 
import Data.Monoid (Monoid)

class Functor ho where
  fmap :: (forall a. f a -> g a) -> ho f -> ho g

class Functor ho => Foldable ho where
  foldMap :: Monoid m => (forall a. f a -> m) -> ho f -> m

class Foldable ho => Traversable ho where
  traverse :: Applicative.Applicative af => (forall a. f a -> af (g a)) -> ho f -> af (ho g)

class Functor ho => Applicative ho where
  pure :: (forall a. f a) -> ho f
  liftA2 :: (forall a. f a -> g a -> h a) -> ho f -> ho g -> ho h

-----

class Singleton ho where
  type Point ho :: k
  singletonIso :: Iso.Iso' (f (Point ho)) (ho f)

toSingleton :: Singleton ho => f (Point ho) -> ho f
toSingleton = view singletonIso

fromSingleton :: Singleton ho => ho f -> f (Point ho)
fromSingleton = view (Iso.from singletonIso)

-----

class ToMaybe ho where
  type ToMaybeCon ho :: * -> Constraint
  toMaybe :: ToMaybeCon ho a => ho f -> Maybe (f a)
