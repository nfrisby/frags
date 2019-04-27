{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Frag (
  -- * Frag Signature
  Frag(Nil),
  type (:+),
  type (:-),

  -- * Frag Families
  FragCard,
  FragEQ,
  FragLT,
  FragNE,

  -- * Frag Evidence
  KnownFragCard,
  SetFrag,
  fragCard,
  fragCard',

  -- * Frag-based 'Type.Reflection.Typeable'
  FragRep(..),
  fragRepZ,
  narrowFragRep,
  widenFragRep,

  -- * Miscellany
  (:/~:)(..),
  Apart,
  ApartPairs(ConsApart,OneApart),
  ProxyInt,
  unsafeProxyInt,
  unsafeConvertProxyInt,
  ) where

import Data.Proxy (Proxy)
import Data.Type.Equality
import GHC.Exts (Int(I#),Int#,Proxy#,proxy#)
import Unsafe.Coerce (unsafeCoerce)

-- | A type-level signed multiset over @k@, /i.e./ an element of a FRee Abelian Group with basis @k@.
--
-- <https://ncatlab.org/nlab/show/free+abelian+group>
--
-- Note that @Frag ()@ is isomorphic to the integers.
--
-- This module adopts the additive flavor for the group signature,
-- and furthermore restricts it to the signed unary/Peano representation of 'Nil', ':+', and ':-'.
data Frag (k :: *) =
    Nil

-- | Increment this basis element's multiplicity.
type family (:+) (fr :: Frag k) (e :: k) :: Frag k where {}
infixl 6 :+

-- | Decrement this basis element's multiplicity.
type family (:-) (fr :: Frag k) (e :: k) :: Frag k where {}
infixl 6 :-

-----

-- | Combined multiplicity of all basis elements.
type family FragCard (fr :: Frag k) :: Frag () where
  FragCard 'Nil = 'Nil

-- | Combined multiplicity of the basis elements equivalent to this one.
type family FragEQ (a :: k) (fr :: Frag k) :: Frag () where
  FragEQ k 'Nil = 'Nil

-- | Combined multiplicity of basis elements less than this one in GHC's arbitrary type ordering.
type family FragLT (a :: k) (fr :: Frag k) :: Frag () where
  FragLT k 'Nil = 'Nil

-- | Basis elements not equivalent to this one.
type family FragNE (a :: k) (fr :: Frag k) :: Frag k where
  FragNE k 'Nil = 'Nil

-----

-- | Implementation detail
newtype ProxyInt (fr :: Frag k) = MkProxyInt Int

-- | Implementation detail
unsafeProxyInt :: forall k. ProxyInt ('Nil :: Frag k)
{-# INLINE unsafeProxyInt #-}
unsafeProxyInt = MkProxyInt 0

-- | Implementation detail
unsafeConvertProxyInt :: forall k fr1 fr2. ProxyInt (fr1 :: Frag k) -> Int# -> ProxyInt (fr2 :: Frag k)
{-# INLINE unsafeConvertProxyInt #-}
unsafeConvertProxyInt (MkProxyInt x) i = MkProxyInt (x + I# i)

-- | Compare to 'KnownNat'.
class KnownFragCard (fr :: Frag k) where method_KnownFragCard :: ProxyInt fr

instance KnownFragCard 'Nil where method_KnownFragCard = MkProxyInt 0

-- | 'fragCard' is the cardinality of the frag.
fragCard :: forall fr. KnownFragCard fr => Proxy fr -> Int
fragCard = \_ -> fragCard' (proxy# :: Proxy# fr)

-- | See 'fragCard'.
fragCard' :: forall fr. KnownFragCard fr => Proxy# fr -> Int
fragCard' = \_ -> let MkProxyInt i = method_KnownFragCard :: ProxyInt fr in i

-- | Each multiplicity is either 0 or 1.
--
-- This is intuitively a class @SetFrag :: Frag k -> Constraint@.
-- But because it can imply type equivalence constraints,
-- we phrase the predicate as a trivial type family equivalence,
-- so that GHC will not float equivalence constraints out from under it.
type family SetFrag (fr :: Frag k) :: () where
  SetFrag 'Nil = '()

-----

-- | Compare to 'Type.Reflection.TypeRep'
data FragRep :: Frag k -> k -> * where
  MkFragRep :: (('Nil :+ '()) ~ FragEQ a fr,KnownFragCard (FragLT a fr)) => FragRep fr a

-- |
fragRepZ :: forall fr a. FragRep fr a -> Int
fragRepZ MkFragRep = fragCard' (proxy# :: Proxy# (FragLT a fr))

instance '() ~ SetFrag fr => TestEquality (FragRep fr) where
  testEquality l r
    | fragRepZ l == fragRepZ r = Just $ unsafeCoerce Refl
    | otherwise = Nothing

-----

-- | Compare to the @Lacks@ axiom from Gaster and Jones.
widenFragRep :: FragRep fr a -> FragRep (fr :+ b) b -> FragRep (fr :+ b) a
{-# INLINE widenFragRep #-}
widenFragRep a@MkFragRep b = unsafeCoerce $
  if fragRepZ a < fragRepZ b then a else {- a + 1 -} fromOffset $ repack $ incr $ unpack $ toOffset a
  where
  incr :: HeapKnownFragCardD fr a -> HeapKnownFragCardD fr a
  incr (MkHeapKnownFragCardD i) = MkHeapKnownFragCardD (i+1)

-- | Compare to the @Lacks@ axiom from Gaster and Jones.
narrowFragRep :: FragRep (fr :+ b) a -> FragRep (fr :+ b) b -> Either (a :~: b) (FragRep fr a)
{-# INLINE narrowFragRep #-}
narrowFragRep a@MkFragRep b = case fragRepZ a `compare` fragRepZ b of
  EQ -> Left (unsafeCoerce Refl)
  LT -> Right $ unsafeCoerce a
  GT -> Right $ unsafeCoerce $
    if fragRepZ a < fragRepZ b then a else {- a - 1 -} fromOffset $ repack $ decr $ unpack $ toOffset a
  where
  decr :: HeapKnownFragCardD fr a -> HeapKnownFragCardD fr a
  decr (MkHeapKnownFragCardD i) = MkHeapKnownFragCardD (i-1)

toOffset :: FragRep fr a -> KnownFragCardD fr a
toOffset MkFragRep = MkKnownFragCardD

fromOffset :: (('Nil :+ '()) ~ FragEQ a fr) => KnownFragCardD fr a -> FragRep fr a
fromOffset MkKnownFragCardD = MkFragRep

unpack :: KnownFragCardD fr a -> HeapKnownFragCardD fr a
unpack = unsafeCoerce

repack :: HeapKnownFragCardD fr a -> KnownFragCardD fr a
repack = unsafeCoerce

data KnownFragCardD :: Frag k -> k -> * where MkKnownFragCardD :: KnownFragCard (FragLT a fr) => KnownFragCardD fr a

-- THIS MUST HAVE THE SAME HEAP REPRESENATION as KnownFragCardD fr
data HeapKnownFragCardD :: Frag k -> k -> * where MkHeapKnownFragCardD :: Int -> HeapKnownFragCardD fr a

-----

-- | Apartness constraint; at least one pair is apart.
--
-- <https://ncatlab.org/nlab/show/apartness+relation>
--
-- We could assert apartness of equal-length tuples of types instead of baking in the list of pairs;
-- however, this approach has no arbitrary upper bound on the length, fewer kind arguments, clearer distinction between itself and userland types, etc.
--
-- DO NOT DECLARE INSTANCES OF THIS CLASS.
--
-- NOTE: This class is necessary for the program logic involving frags,
-- but its logic does not inherently depend on frags.
-- Unfortunately, neither GHC nor some other plugin currently provides apartness constraints.
class Apart (pairs :: ApartPairs) where {}

-- TODO is it safe for GHC to float equalities past these?

-- TODO if GHC should float apartness constraints, then we'll have to encode them as equalities somehow.
-- But I don't think it should float them, so confirm that somehow.

-- | Base instance.
--
-- DO NOT DECLARE INSTANCES OF THIS CLASS.
instance Apart ('OneApart 'False 'True)

-- | See 'Apart'.
data ApartPairs =
    forall k.   -- TODO need hetero?
    ConsApart k k ApartPairs
  |
    forall k.   -- TODO need hetero?
    OneApart k k

-- | A proof that two types are apart; analogous to '(:~:).
data (:/~:) a b = Apart ('OneApart a b) => MkApart
