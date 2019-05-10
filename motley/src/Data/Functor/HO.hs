{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

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
  -- *
  type (~>)(..),
  ) where

import qualified Control.Applicative as Applicative
import Control.Lens (view)
import qualified Control.Lens.Iso as Iso
import Data.Kind (Constraint)
import Data.Maybe (Maybe) 
import Data.Monoid (Monoid)

infixr 0 ~>
newtype (~>) f g a = MkFun{appFun :: f a -> g a}

-----

class Functor ho where
  infixl 4 <$>
  (<$>),fmap,liftA :: (forall a. f a -> g a) -> ho f -> ho g

  (<$>) = fmap
  fmap = liftA
  liftA = (<$>)

  {-# MINIMAL (<$>) | fmap | liftA #-}

class Functor ho => Foldable ho where
  foldMap :: Monoid m => (forall a. f a -> m) -> ho f -> m

class Foldable ho => Traversable ho where
  traverse :: Applicative.Applicative af => (forall a. f a -> af (g a)) -> ho f -> af (ho g)

class Functor ho => Applicative ho where
  infixl 4 <*>
  (<*>) :: ho (f ~> g) -> ho f -> ho g
  liftA2 :: (forall a. f a -> g a -> h a) -> ho f -> ho g -> ho h
  pure :: (forall a. f a) -> ho f

  (<*>) = liftA2 appFun
  liftA2 fun fs gs = (\f -> MkFun (fun f)) <$> fs <*> gs

  {-# MINIMAL pure,(<*>) | pure,liftA2 #-}

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
