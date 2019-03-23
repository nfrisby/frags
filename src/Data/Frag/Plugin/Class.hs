{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}

module Data.Frag.Plugin.Class (
  Env(..),
  simplify,
  ) where

import Control.Monad (guard)
import Data.Monoid (All(..),First(..))

import qualified Data.Frag.Plugin.Frag as Frag
import qualified Data.Frag.Plugin.Equivalence.NilNil as NilNil
import Data.Frag.Plugin.Types

data Env b r = MkEnv{
    envEq :: !(b -> b -> Maybe Bool)
  ,
    -- | Is it nil, regardless of kind argument?
    envIsNil :: !(r -> Bool)
  ,
    -- | INVARIANT: no root is nil
    envMultiplicity :: !(FM (r,b) Count)
  ,
    envPassThru :: !(Frag.Env b r)
  }

reinterpret :: (Key b,Key r,Monad m) => Env b r -> FragClass b r -> AnyT m (FragClass b r)
reinterpret env = \case
  KnownFragZ fr delta -> KnownFragZ <$> f fr <*> pure delta
  SetFrag fr -> SetFrag <$> f fr
  where
  f = Frag.reinterpret (envPassThru env)

simplify :: (Key b,Key r,Monad m) => Env b r -> FragClass b r -> AnyT m (Contra (Derived b b,FragClass b r))
simplify env freq = reinterpret env freq >>= simplify_ env

simplify_ :: (Key b,Key r,Monad m) => Env b r -> FragClass b r -> AnyT m (Contra (Derived b b,FragClass b r))
simplify_ env = \case
  KnownFragZ fr delta
    | nullFM fm -> pure $ OK (emptyDerived,KnownFragZ fr delta)
    | otherwise -> do
    setM True
    simplify env $ KnownFragZ fr{fragExt = emptyExt} (delta + foldMap id fm)
    where
    fm = unExt (fragExt fr)
  SetFrag fr -> case pop env fr of
    Just (_,count,fr') -> do
      setM True
      if 0 <= count && count <= 1
        then simplify env $ SetFrag fr'
        else pure Contradiction
    Nothing
      | envIsNil env root -> case m_all_solo of
      Just bs -> do
        let neqs = mk_neqs emptyFM bs
        setM $ not (nullFM neqs)
        pure $ OK (emptyDerived{dneqs=neqs},SetFrag (MkFrag emptyExt root))
      Nothing -> do
        (neg,pos,eqs) <- mk_eqs
        pure $ OK (emptyDerived{deqs=eqs},SetFrag (MkFrag (pos `subtractExt` neg) root))
      | otherwise -> pure $ OK (emptyDerived,SetFrag fr)
    where
    ext = fragExt fr
    root = fragRoot fr

    m_all_solo = foldlExt ext (Just []) $ \acc b count -> if
      | 0 == count -> acc
      | 1 == count -> maybe acc (Just . (b:)) acc
      | otherwise -> Nothing

    -- Set ('Nil :+ a :+ b :+ c :+ d)   if and only if   a /~ b,a /~ c,a /~ d,b /~ c,b /~ d,c /~ d
    mk_neqs acc = \case
      [] -> acc
      b:bs -> acc' `seq` mk_neqs acc' bs
        where
        acc' = foldl (flip $ \r -> insertFMS (b,r) ()) acc bs

    -- is not definitely apart
    notApart l r = maybe True not $ envEq env l r

    mk_eqs = do
      let
        MkNegPosExt neg _ pos _ = splitExt ext
        eqs = emptyFM
        too_pos = filterExt (\_ count -> count > 1) pos
      -- decrease extras
      (pos',neg',eqs') <- case NilNil.find_oneside_matches notApart too_pos neg of
        Just (Right x) -> do setM True; pure $ NilNil.enact eqs x pos neg (flip (,))
        _ -> pure (pos,neg,eqs)
      -- increase missing
      case NilNil.find_oneside_matches notApart neg' pos' of
        Just (Right x) -> do setM True; pure $ NilNil.enact eqs' x neg' pos' (,)
        _ -> pure (neg',pos',eqs')

-- | @Just@ if and only if the popped element absolutely has 0 multiplicity in the remaining frag
-- (e.g. independent of variable substitutions).
--
-- TODO implement via NilNil.find_oneside_matches ?
pop :: (Key b,Key r) => Env b r -> Frag b r -> Maybe (b,Count,Frag b r)
pop env fr
  | envIsNil env r = frst_ext
  | otherwise = frst_root
  where
  ext = fragExt fr
  r = fragRoot fr

  pop_ext b
    | getAll $ flip foldMapFM fm' $ \b' count' -> All $ 0 == count' || maybe False not (envEq env b b')
    = Just (maybe 0 id $ lookupFM b (unExt ext),MkExt fm')

    | otherwise = Nothing
    where
    fm = unExt ext
    fm' = alterFM b (\_ -> Nothing) fm

  frst_ext = getFirst $ flip foldMapFM (unExt ext) $ \b count -> First $ do
    guard $ 0 /= count
    (_,ext') <- pop_ext b
    Just (b,count,fr{fragExt=ext'})

  frst_root = do
    fm <- lookupFM r $ unTuple2FM (envMultiplicity env)
    getFirst $ flip foldMapFM fm $ \b count_root -> First $ do
      (count_ext,ext') <- pop_ext b
      let count = count_root + count_ext
      guard $ 0 /= count
      Just (b,count,fr{fragExt=insertExt b (invertSign count_root) ext'})
