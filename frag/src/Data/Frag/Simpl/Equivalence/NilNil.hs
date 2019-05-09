{-# LANGUAGE PatternGuards #-}

module Data.Frag.Simpl.Equivalence.NilNil (
  enact,
  find_oneside_matches,
  simplify,
  ) where

import Control.Monad (guard)
import Data.Either (partitionEithers)
import Data.Maybe (listToMaybe)

import Data.Frag.Simpl.Types

simplify :: (Key b) => (b -> b -> Bool) -> Ext b -> Maybe (Contra (Derived b b,Ext b))
simplify notApart ext
  -- contradiction: 'Nil ~ 'Nil :+ a :+ b :- c
  | neg_count /= pos_count = Just Contradiction

  | otherwise = case match_result of
      Contradiction -> Just Contradiction
      OK (neg',pos',eqs)
        -- unification: 'Nil ~ 'Nil :+ a :- b   requires   a ~ b
        | not (nullFM eqs) -> Just $ OK $ (emptyDerived{deqs=eqs},pos' `subtractExt` neg')
      _ -> Nothing

  where
  MkNegPosExt neg neg_count pos pos_count = splitExt ext
  match_result = matches notApart neg pos emptyFM

matches :: (Key l,Key r) => (l -> r -> Bool) -> Ext l -> Ext r -> FM (l,r) () -> Contra (Ext l,Ext r,FM (l,r) ())
matches notApart lext rext fm
  | Just insight <- find_oneside_matches notApart lext rext = case insight of
    Left _l -> Contradiction
    Right (l,rs,count) -> matches notApart lext' rext' fm'
      where
      (lext',rext',fm') = enact fm (l,rs,count) lext rext (,)

  | Just insight <- find_oneside_matches (flip notApart) rext lext = case insight of
    Left _r -> Contradiction
    Right (r,ls,count) -> matches notApart lext' rext' fm'
      where
      (rext',lext',fm') = enact fm (r,ls,count) rext lext (flip (,))

  | otherwise = OK (lext,rext,fm)

enact :: (Key l,Key r,Key lr) => FM lr () -> (l,[r],Count) -> Ext l -> Ext r -> (l -> r -> lr) -> (Ext l,Ext r,FM lr ())
enact fm (x,ys,count) xext yext xy = let
  xext' = insertExt x (invertSign count) xext   -- remove count-many of x
  yext' = filterExt predicate yext   -- remove all of the ys
    where
    predicate y kount = case lookupFM y (fromListFMSet ys) of
      Nothing -> 0 /= kount
      Just () -> False
  fm' = foldl (\acc y -> insertFMS (xy x y) () acc) fm ys
  in
  (xext',yext',fm')

-- @Left@ means contradiction: this l is apart from all the rs.
-- @Right (l,[r],k)@ means unification: l is apart from all other rs, and there are at least as many of l as there are of these rs.
find_oneside_matches :: (Key l,Key r) => (l -> r -> Bool) -> Ext l -> Ext r -> Maybe (Either l (l,[r],Count))
find_oneside_matches notApart lext rext = post $ do
  -- list monad
  (l,count) <- toListFM (unExt lext)
  let
    candidates = filter (notApart l . fst) $ toListFM (unExt rext)
    total = sum (map snd candidates)
  if total <= 0 then pure $ Left l else do
    guard (total <= count)
    pure $ Right (l,map fst candidates,total)

  where
  post x = listToMaybe $ map Left lefts ++ map Right rights
    where
    (lefts,rights) = partitionEithers x
