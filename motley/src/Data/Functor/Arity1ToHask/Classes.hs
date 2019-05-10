{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | This module defines type classes
-- indexed by functors (to @*@) from @k -> *@ (\"arity 1, to Hask\").
-- Such types internally apply their arguments to fixed types
-- (or pass them to other types that do so, or so on).
--
-- Examples include
--
-- * @newtype AtInt f = MkAtInt{atInt :: f Int}@,
-- * @At a@ given @newtype At a f = MkAt{at :: f a}@,
-- * @Product a b@ given @data Product a b f = MkProduct (a f) (b f)@ if @a@ and @b@ are examples,
-- * and so on.
module Data.Functor.Arity1ToHask.Classes (
  -- * Standard Classes
  Applicative(..),
  Foldable(..),
  Functor(..),
  Traversable(..),
  -- * Non-standard classes
  fromSingleton,
  toSingleton,
  Singleton(..),
  ToMaybe(..),
  ) where

import qualified Control.Applicative as Applicative
import Control.Lens (view)
import qualified Control.Lens.Iso as Iso
import Data.Functor.Fun (type (~>),pattern MkFun,appFun)
import Data.Kind (Constraint)
import Data.Maybe (Maybe) 
import Data.Monoid (Monoid)

-----

class Functor ff where
  infixl 4 <$>
  (<$>),fmap,liftA :: (forall a. f a -> g a) -> ff f -> ff g

  (<$>) = fmap
  fmap = liftA
  liftA = (<$>)

  {-# MINIMAL (<$>) | fmap | liftA #-}

class Functor ff => Foldable ff where
  foldMap :: Monoid m => (forall a. f a -> m) -> ff f -> m

class Foldable ff => Traversable ff where
  traverse :: Applicative.Applicative af => (forall a. f a -> af (g a)) -> ff f -> af (ff g)

class Functor ff => Applicative ff where
  infixl 4 <*>
  (<*>) :: ff (f ~> g) -> ff f -> ff g
  liftA2 :: (forall a. f a -> g a -> h a) -> ff f -> ff g -> ff h
  pure :: (forall a. f a) -> ff f

  (<*>) = liftA2 appFun
  liftA2 fun fs gs = (\f -> MkFun (fun f)) <$> fs <*> gs

  {-# MINIMAL pure,(<*>) | pure,liftA2 #-}

-----

class Singleton ff where
  type Point ff :: k
  singletonIso :: Iso.Iso' (f (Point ff)) (ff f)

toSingleton :: Singleton ff => f (Point ff) -> ff f
toSingleton = view singletonIso

fromSingleton :: Singleton ff => ff f -> f (Point ff)
fromSingleton = view (Iso.from singletonIso)

-----

class ToMaybe ff where
  type ToMaybeCon ff :: * -> Constraint
  toMaybe :: ToMaybeCon ff a => ff f -> Maybe (f a)
