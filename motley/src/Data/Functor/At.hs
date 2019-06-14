{-# LANGUAGE PolyKinds #-}

-- | A basic functor missing from @base@.
module Data.Functor.At (
  At(..),
  ) where

-- |
newtype At (a :: k) (f :: k -> *) = MkAt{
    -- |
    getAt :: f a
  }

instance Show (f a) => Show (At a f) where
  showsPrec p = showsPrec p . getAt
