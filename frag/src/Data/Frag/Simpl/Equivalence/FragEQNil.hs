{-# LANGUAGE LambdaCase #-}

module Data.Frag.Simpl.Equivalence.FragEQNil (
  simplify,
  ) where

import Data.Monoid (All(..),Any(..))

import Data.Frag.Simpl.Types

data Acc l r = MkAcc (FM (l,r) ()) !Count (FM (l,r) ()) !Count

simplify :: (Key l,Key r,Key x) => (r -> r -> Bool) -> l -> Ext r -> Ext x -> Maybe (Contra (Derived l r))
simplify notApart b0 eq_ext ext
  -- contradiction: FragEQ a ('Nil :+ a) ~ 'Nil :+ '() :+ '()
  | total < negate neg_count || pos_count < total = Just Contradiction

  -- unification: FragEQ x ('Nil :+ a :- b) ~ 'Nil :+ '()   to x ~ a, x /~ b
  --
  -- NB If any of those individual comparisons could be immediately decided,
  -- they should have been reduced out of the FragEQ application before reaching this point.
  | negate neg_count == total = Just $ ok $ MkDerived{deqs=neg,dneqs=pos}
  | pos_count == total = Just $ ok $ MkDerived{deqs=pos,dneqs=neg}

  | otherwise = Nothing
  where
  MkAcc neg neg_count pos pos_count = foldlExt eq_ext (MkAcc emptyFM mempty emptyFM mempty) $ \st@(MkAcc n ncount p pcount) b count ->
    case compare count 0 of
      LT -> MkAcc (insertFMS (b0,b) () n) (ncount - count) p pcount
      EQ -> st
      GT -> MkAcc n ncount (insertFMS (b0,b) () p) (pcount + count)

  total = foldMap id (unExt ext)

  ok deriv = if incompatible notApart deriv
    then Contradiction  -- contradiction: FragEQ x ('Nil :+ 1 .+ 2) ~ 'Nil :+ '() :+ '()
    else OK deriv

incompatible :: (Key l,Key r) => (r -> r -> Bool) -> Derived l r -> Bool
incompatible notApart derived =
  getAny $ eqs <> neqs
  where
  -- For each l (there's only one when in a FragEQ-Nil equivalence), confirm none of its rs are pairwise notApart.
  --
  --   e.g. (l ~ 1,l ~ 2) is contradiction by transitivity
  --
  -- Catching it early here gives a better error message.
  eqs = flip foldMap (unTuple2FM (deqs derived)) $ \rfm ->
      (Any . not . getAll)
    $
      go (map fst $ toListFM rfm)
    where
    go = \case
      [] -> mempty
      r:rs -> foldMap (All . notApart r) rs <> go rs

  -- Make sure each (l,r) pair is not notApart
  neqs = mempty   -- by INVARIANT: the FragEQ l (... .+- r ...) would have reduced already
