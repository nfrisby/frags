{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}

module Data.Frag.Plugin.Frag (
  Env(..),
  envFrag_out,
  interpret,
  reinterpret,
  ) where

import Data.Monoid (Endo(..),Sum(..),getAny)

import Data.Frag.Plugin.Types

interpret :: (Key b,Monad m) => Env k b r -> RawFrag b r -> AnyT m (Frag b r)
interpret env = let ?env = env in interpret_

reinterpret :: (Key b,Monad m) => Env k b r -> Frag b r -> AnyT m (Frag b r)
reinterpret env fr = interpret env $ flattenRawFrag $ envRawFrag_out env <$> forgetFrag fr

envFrag_out :: Key b => Env k b r -> RawFrag b r -> Frag b r
envFrag_out env r
  | getAny hit = error "non-canonical argument to envFrag_out"
  | otherwise = a
  where
  (hit,a) = runAny (interpret env r) mempty

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
    envIsNil :: !(r -> Bool)
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
  ,
    envZBasis :: !k
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

-- | @mkFrag ext r@ is the frag resulting from peeling an extension off @r@
-- and combining it with @ext@.
--
-- Extensions are so combined only within reduction rules. Thus:
--
-- * Always calls @'setM' True@,
-- * ASSUMPTION: @r@ is already canonical.
mkFrag :: (Key b,Monad m,?env :: Env k b r) => Ext b -> r -> AnyT m (Frag b r)
mkFrag ext r = do
  setM True
  pure $ MkFrag (go ext (rawFragExt raw)) (rawFragRoot raw)
  where
  raw = envRawFrag_out ?env r
  go acc = \case
    ExtRawExt e s b -> go (insertExt b (applySign s 1) acc) e
    NilRawExt -> acc

interpretFunRoot :: (Key b,Monad m,?env :: Env k b r) => Ext b -> FunRoot k b (Frag b r) -> AnyT m (Frag b r)
interpretFunRoot outer_ext (MkFunRoot knd fun fr)
  | envIsZBasis ?env knd = do
  -- reduced: FragCard fr   to   fr
  --          FragEQ b fr   to   fr
  --          FragLT b fr   to   'Nil
  --          FragNE b fr   to   'Nil
  setM True
  let
    fr' = fr{fragExt = outer_ext `addExt` inner_ext}
    zero = MkFrag outer_ext $ envNil ?env knd
  pure $ case fun of
    FragCard -> fr'
    FragEQ _ -> fr'
    FragLT _ -> zero
    FragNE _ -> zero

  | nullFM (unExt inner_ext)
  , envIsNil ?env (fragRoot fr) = do
  -- reduced: FragCard 'Nil   to   'Nil
  --          FragEQ b 'Nil   to   'Nil
  --          FragLT b 'Nil   to   'Nil
  --          FragNE b 'Nil   to   'Nil
  setM True
  pure $ MkFrag outer_ext $ envNil ?env $ case fun of
    FragCard -> envZBasis ?env
    FragEQ{} -> envZBasis ?env
    FragLT{} -> envZBasis ?env
    FragNE{} -> knd

  -- reduced:
  --   FragEQ a (FragNE a rNE ...)   to   FragEQ a ('Nil ...)
  --   FragEQ a (FragNE b rNE ...)   to   FragEQ a (rNE ...)   if a ~/ b
  | FragEQ a <- fun
  , Just (b,rNE) <- innerNE
  , Just eq <- envIsEQ ?env a b =
    recurWithReducedRoot $ if eq then envNil ?env (envZBasis ?env) else rNE

  -- reduced:
  --   FragLT a (FragNE b rNE ...)   to   FragLT a (rNE ...)   if b DET>= a
  | FragLT a <- fun
  , Just (b,rNE) <- innerNE
  , Just False <- envIsLT ?env b a = recurWithReducedRoot rNE

  -- reduced:
  --   FragNE a (FragNE a rNE ...)   to   FragNE a (rNE ...)
  | FragNE a <- fun
  , Just (b,rNE) <- innerNE
  , EQ <- compareViaFM a b = recurWithReducedRoot rNE

  -- unsorted:
  --   FragNE a (FragNE b rNE)   to   FragNE b (FragNE a rNE)   if b NONDET< a
  | FragNE a <- fun
  , nullFM (unExt inner_ext)
  , Just (b,rNE) <- innerNE
  , LT <- compareViaFM b a = do
  setM True
  interpretFunRoot outer_ext $ MkFunRoot knd (FragNE b) $ MkFrag emptyExt $
    envFunRoot_inn ?env (MkFunRoot knd fun rNE)

  -- reduced:
  --   FragNE a fr   to   fr   if 'Nil ~ FragEQ a fr
  | FragNE a <- fun
  , nullFM (unExt inner_ext)
  , let r = envFrag_inn ?env fr
  , Just 0 <- envMultiplicity ?env r a = mkFrag outer_ext r

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
  innerNE = case envFunRoot_out ?env inner_root of
    Just (MkFunRoot _ (FragNE b) rNE) -> Just (b,rNE)
    _ -> Nothing
  recurWithReducedRoot r =
    mkFrag inner_ext r >>= interpretFunRoot outer_ext . MkFunRoot knd fun

  reduction = red_root || red'
  outer_ext' = addExt pop' $ insertExt (envUnit ?env) (units_root + units') outer_ext

  inner_root = fragRoot fr
  (inner_root',red_root,units_root)
    | FragEQ b <- fun
    , Just k <- envMultiplicity ?env inner_root b
    = (envNil ?env knd,True,k)

    | otherwise = (inner_root,False,0)

  inner_ext = fragExt fr
  inner_ext' = keep'
  (pop',units',keep',red') = foldlExt inner_ext (emptyExt,0,emptyExt,False) $ \parts@(pop,units,keep,red) b count ->
    if 0 == count then parts else case predicate b of
      Count -> let x = units + count in x `seq` (pop,x,keep,True)
      Drop -> (pop,units,keep,True)
      Keep -> let x = insertExt b count keep in x `seq` (pop,units,x,red)
      Pop -> let x = insertExt b count pop in x `seq` (x,units,keep,True)

  predicate b' = case fun of
    FragCard -> Count
    FragEQ b -> case envIsEQ ?env b' b of
      Nothing -> Keep
      Just False -> Drop
      Just True -> Count
    FragLT b -> case envIsLT ?env b' b of
      Nothing -> Keep
      Just False -> Drop
      Just True -> Count
    FragNE b -> case not <$> envIsEQ ?env b' b of
      Nothing -> Keep
      Just False -> Drop
      Just True -> Pop

data PredicateResult b =
    Count
  |
    Drop
  |
    Keep
  |
    Pop
