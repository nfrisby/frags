{-# LANGUAGE PolyKinds #-}

module Data.Functor.At (
  At(..),
  ) where

newtype At (a :: k) (rep :: k -> *) = MkAt{getAt :: rep a}

instance Show (rep a) => Show (At a rep) where
  showsPrec p = showsPrec p . getAt
