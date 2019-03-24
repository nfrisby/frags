{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}

module Data.Frag.Plugin.Frag (
  Env(..),
  interpret,
  reinterpret,
  ) where

import Data.Monoid (Endo(..),Sum(..))

import Data.Frag.Plugin.Types

interpret :: (Key b,Monad m) => Env k b r -> RawFrag b r -> AnyT m (Frag b r)
interpret env = let ?env = env in interpret_

reinterpret :: (Key b,Monad m) => Env k b r -> Frag b r -> AnyT m (Frag b r)
reinterpret env fr = interpret env $ flattenRawFrag $ envRawFrag_out env <$> forgetFrag fr

-----

data Env k b r = MkEnv{
    -- |
    envFrag_inn :: !(Frag b r -> r)
  ,
    -- | Not expected to un-unflatten.
    envFunRoot_inn :: !(FunRoot k b r -> r)
  ,
    -- |
    envFunRoot_out :: !(r -> Maybe (FunRoot k b r))
  ,
    envIsEQ :: !(b -> b -> Maybe Bool)
  ,
    -- | Returns @Just@ if and only if the order is deterministic.
    -- (e.g. independent of variable substitutions).
    envIsLT :: !(b -> b -> Maybe Bool)
  ,
    envIsZBasis :: !(k -> Bool)
  ,
    envMultiplicity :: !(r -> b -> Maybe Count)
  ,
    envNil :: !(k -> r)
  ,
    -- | INVARIANT: Yields the longest extension possible.
    envRawFrag_out :: !(r -> RawFrag b r)
  ,
    -- |
    envUnit :: !b
  }

interpret_ :: (Key b,Monad m,?env :: Env k b r) => RawFrag b r -> AnyT m (Frag b r)
interpret_ raw_fr = do
  ext <- interpretRawExt_ (rawFragExt raw_fr)
  interpretRawRoot_ ext (rawFragRoot raw_fr)

-- | INVARIANT: If the result has a non-empty extension, the flag is set.
interpretRawRoot_ :: (Key b,Monad m,?env :: Env k b r) => Ext b -> r -> AnyT m (Frag b r)
interpretRawRoot_ ext r = case envFunRoot_out ?env r of
  Just (MkFunRoot knd fun inner_r) ->
    -- It's important to not unfold @FunRoot@s needlessly;
    -- see note in 'Data.Frag.Plugin.Equivalence.interpret'.
    preferM (MkFrag ext r) $ do
      interpret_ (envRawFrag_out ?env inner_r) >>= interpretFunRoot ext . MkFunRoot knd fun
  Nothing -> pure $ MkFrag ext r

-----

interpretRawExt_ :: (Key b,Monad m) => RawExt b -> AnyT m (Ext b)
interpretRawExt_ = go 0 emptyFM
  where
  go !i !fm = \case
    ExtRawExt raw_ext s b -> go (i + 1) fm' raw_ext
      where
      fm' = insertFMS b (applySign s 1,mkPos i) fm
    NilRawExt -> do
      let
        changed = isChanged $ (`appEndo` ExpectingFirst 0) $ flip foldMap fm $ \(count,pos) ->
          Endo $ \check -> case (pos,check) of
            (Contiguous frst next,ExpectingFirst expected)
              | frst == expected    -- collated-but-not-sorted: +b +a +a   to   +a +a +b
              , next - frst == abs (getSum (unCount count))   -- cancelable: +a -a +b   to   +b
              -> ExpectingFirst next
            _ -> Changed    -- uncollated: +a +b +a   to   +a +a +b

      setM changed
      pure $ (`appEndo` emptyExt) $ flip foldMapFM fm $ \b (count,_) ->
        Endo $ \acc -> if 0 == count then acc else insertExt b count acc

data Pos =
    Contiguous !Int !Int
  |
    Incontiguous

instance Semigroup Pos where
  Contiguous first1 next1 <> Contiguous first2 next2
    | next1 == first2 = Contiguous first1 next2
    | next2 == first1 = Contiguous first2 next1
  _ <> _ = Incontiguous

mkPos :: Int -> Pos
mkPos = \p -> Contiguous p (p+1)

-----

interpretFunRoot :: (Key b,Monad m,?env :: Env k b r) => Ext b -> FunRoot k b (Frag b r) -> AnyT m (Frag b r)
interpretFunRoot outer_ext (MkFunRoot knd fun fr)
  | envIsZBasis ?env knd = do
  -- reduced: FragCard fr   to   fr
  --          FragEQ b fr   to   fr
  --          FragLT b fr   to   'Nil
  setM True
  pure $ case fun of
    FragCard -> fr
    FragEQ _ -> fr
    FragLT _ -> MkFrag emptyExt $ envNil ?env knd

  | otherwise = do
  -- reduced:   FragEQ a (0 +a +b)   to   '() :+ FragEQ a (0 :+ b)
  --          or
  --            FragEQ C (0 +a +D)   to   FragEQ C (0 :+ a)
  --
  --          and/or
  --            FragEQ C (x ...)   to   FragEQ C (0 ...) :+ k    if FragEQ C x ~ k in environment
  setM reduction
  pure $ if reduction
    then MkFrag outer_ext' $ envFunRoot_inn ?env $ MkFunRoot knd fun $ envFrag_inn ?env $ MkFrag inner_ext' inner_root'
    else MkFrag outer_ext $ envFunRoot_inn ?env $ MkFunRoot knd fun $ envFrag_inn ?env fr
  where
  reduction = red_root || red'
  outer_ext' = insertExt (envUnit ?env) (pop_root + pop') outer_ext

  inner_root = fragRoot fr
  (inner_root',red_root,pop_root)
    | FragEQ b <- fun
    , Just k <- envMultiplicity ?env inner_root b
    = (envNil ?env knd,True,k)

    | otherwise = (inner_root,False,0)

  inner_ext = fragExt fr
  inner_ext' = keep'
  (pop',keep',red') = foldlExt inner_ext (0,emptyExt,False) $ \parts@(pop,keep,red) b count ->
    if 0 == count then parts else case predicate b of
      Nothing -> let x = insertExt b count keep in x `seq` (pop,x,red)   -- keep if no decision
      Just False -> (pop,keep,True)   -- drop if fail
      Just True -> let x = pop + count in x `seq` (x,keep,True)   -- count if pass

  predicate b' = case fun of
    FragCard -> Just True
    FragEQ b -> envIsEQ ?env b' b
    FragLT b -> envIsLT ?env b' b
