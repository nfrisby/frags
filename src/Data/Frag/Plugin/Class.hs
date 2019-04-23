{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}

module Data.Frag.Plugin.Class (
  Env(..),
  Simplified(..),
  simplify,
  ) where

import Data.Monoid (All(..))
import Data.List.NonEmpty (NonEmpty((:|)))

import qualified Data.Frag.Plugin.Frag as Frag
import Data.Frag.Plugin.Types

singleton :: a -> NonEmpty a
singleton = pure

data Env k b r = MkEnv{
    envEq :: !(b -> b -> Maybe Bool)
  ,
    envIsSet :: !(r -> Bool)
  ,
    envPassThru :: !(Frag.Env k b r)
  }

reinterpret :: (Key b,Key r,Monad m) => Env k b r -> FragClass b r -> AnyT m (FragClass b r)
reinterpret env = \case
  KnownFragZ fr delta -> KnownFragZ <$> f fr <*> pure delta
  SetFrag fr -> SetFrag <$> f fr
  where
  f = Frag.reinterpret (envPassThru env)

-----

data Simplified k b r =
    SimplClass !(NonEmpty (k,FragClass b r))
  |
    SimplFragEQ !k !b !Bool !r
  deriving (Eq,Show)

simplify :: (Key b,Key r,Monad m) => Env k b r -> k -> FragClass b r -> AnyT m (Contra (Derived b b,Simplified k b r))
simplify env k freq = reinterpret env freq >>= simplify_ env k

trivial :: Key b => Env k b r -> k -> FragClass b r
trivial env k = SetFrag $ MkFrag emptyExt $ Frag.envNil (envPassThru env) k

contradiction :: Monad m => AnyT m (Contra x)
contradiction = do setM True; pure Contradiction

ok1 :: (Applicative m,Key b) => k -> FragClass b r -> m (Contra (Derived b b,Simplified k b r))
ok1 k x = pure $ OK (emptyDerived,SimplClass $ singleton (k,x))

simplify_ :: (Key b,Key r,Monad m) => Env k b r -> k -> FragClass b r -> AnyT m (Contra (Derived b b,Simplified k b r))
simplify_ env k = \case
  KnownFragZ fr delta
    | nullFM fm -> ok fr delta
    -- reduction:
    --   KnownFragZ (p :+- x) delta   to   KnownFragZ p (delta +- 1)
    | otherwise -> do
    setM True
    ok fr{fragExt = emptyExt} (delta + foldMap id fm)
    where
    fm = unExt (fragExt fr)
    ok fr' delta' = ok1 k (KnownFragZ fr' delta')
  SetFrag fr
    -- stuck:
    --     SetFrag 'Nil
    | Frag.envIsNil fragEnv root && nullFM fm -> stuck

    -- reduction:
    --    SetFrag (FragNE b p)   to   SetFrag 'Nil   if SetFrag p
    | nullFM fm
    , envIsSet env neqs_arg -> do setM True; ok1 k (trivial env k)

    -- reduction:
    --    SetFrag (FragNE b p)   to   SetFrag p   if 0 <= p(b) <= 1
    | not (nullFM neqs)
    , nullFM fm
    , getAll $ flip foldMapFM neqs $ \b () -> All $ case Frag.envMultiplicity fragEnv neqs_arg b of
        Just count -> 0 <= count && count <= 1
        Nothing -> False
    -> do setM True; ok1 k $ SetFrag $ MkFrag emptyExt neqs_arg

    -- reduction:
    --   SetFrag (FragNE b ('Nil :+ x))   to   SetFrag 'Nil
    | not (nullFM neqs)
    , nullFM fm
    , MkRawFrag (ExtRawExt NilRawExt Pos _) arg_root <- Frag.envRawFrag_out fragEnv neqs_arg
    , Frag.envIsNil fragEnv arg_root -> do setM True; ok1 k (trivial env k)

    -- SetFrag (...) :: Frag ()
    | Frag.envIsZBasis fragEnv k -> simplifyZBasis env k fr

    -- SetFrag p
    | nullFM fm -> stuck

    -- reduction:
    --   SetFrag (p :+- a)   to   (SetFrag (FragEQ a p :+- '()),SetFrag (FragNE a p))
    | otherwise -> do
      setM True
      let
      pure $ OK $ (,) emptyDerived $ SimplClass $ ((k,trivial env k) :|) $ foldlExt ext [] $ \acc b count ->
        if 0 == count then acc else
        let
          f k' ext' fun = (,) k' $ SetFrag $ MkFrag ext' $ Frag.envFunRoot_inn fragEnv $
            MkFunRoot k (fun b) $ Frag.envFrag_inn fragEnv fr{fragExt = insertExt b (invertSign count) ext}
        in f (Frag.envZBasis fragEnv) (insertExt (Frag.envUnit fragEnv) count emptyExt) FragEQ :
           f k emptyExt FragNE :
           acc

    where
    fragEnv = envPassThru env

    (_,(neqs,neqs_arg)) = flip runAny mempty $ Frag.envFragNE_out fragEnv (fragRoot fr)

    fm = unExt ext
    ext = fragExt fr
    root = fragRoot fr

    stuck = ok1 k (SetFrag fr)

-----

simplifyZBasis :: (Monad m,Key b) => Env k b r -> k -> Frag b r -> AnyT m (Contra (Derived b b,Simplified k b r))
simplifyZBasis env k fr
  -- SetFrag (FragEQ b ('Nil ...) ...)
  | Just (MkFunRoot keq (FragEQ b) arg) <- Frag.envFunRoot_out fragEnv root
  , let inner_fr = Frag.envFrag_out fragEnv arg
  , Frag.envIsNil fragEnv (fragRoot inner_fr) =
  deriveZBasis env k keq b inner_fr ext tot

  -- SetFrag (FragEQ b fr :+- a)   to   FragEQ b fr ~ 'Nil :+? a   if SetFrag fr
  | Just (MkFunRoot keq (FragEQ b) arg) <- Frag.envFunRoot_out fragEnv root
  , envIsSet env arg
  , 1 == abs tot = do
    setM True;
    pure $ OK (emptyDerived,SimplFragEQ keq b (1 /= tot) arg)

  -- SetFrag (FragEQ b fr :+- a :+- a)   to   _|_   if SetFrag fr
  | Just (MkFunRoot _ (FragEQ _) arg) <- Frag.envFunRoot_out fragEnv root
  , envIsSet env arg
  , 1 < abs tot = contradiction

  -- SetFrag ('Nil :+- a ... :: Frag ())
  | Frag.envIsNil fragEnv root && not (nullFM fm) =
  if tot < 0 || 1 < tot
  -- contradiction:
  --     SetFrag ('Nil :- a :: Frag ())   to   _|_
  --     SetFrag ('Nil :+ a :+ b :: Frag ())   to   _|_
  then contradiction
  -- reduction:
  --     SetFrag ('Nil :+ (a :: ()))   to   SetFrag 'Nil
  else do setM True; ok1 k (trivial env k)

  | otherwise = stuck

  where
  fragEnv = envPassThru env

  fm = unExt ext
  tot = foldMap id fm
  ext = fragExt fr
  root = fragRoot fr

  stuck = ok1 k (SetFrag fr)

deriveZBasis :: (Monad m,Key b) => Env k b r -> k -> k -> b -> Frag b r -> Ext b -> Count -> AnyT m (Contra (Derived b b,Simplified k b r))
deriveZBasis env k keq b inner_fr ext tot = case mding' of
  Contradiction -> contradiction
  OK ding' -> do
    let
      reduced =   -- reduction:
          -- SetFrag (FragEQ b ('Nil :- x) :+ u)   to   SetFrag 'Nil
          (1 == ding_tot ding' && 1 == ding_neg ding' && 0 == ding_pos ding')
        ||
          -- SetFrag (FragEQ b ('Nil :+ x))   to   SetFrag 'Nil
          (0 == ding_tot ding' && 0 == ding_neg ding' && 1 == ding_pos ding')
      -- derived:
      --     SetFrag (FragEQ b ('Nil :- y) :+ '() :+ '())   to   (b ~ y,SetFrag ((FragEQ b 'Nil) :+ '()))
      --                                                                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
      --                                                                reducible, but yielding due to deqs anyway
      derived = differentDeriving ding ding'
      c = if reduced then trivial env k else
        SetFrag $ MkFrag (ding_ext_outer ding') $
        Frag.envFunRoot_inn fragEnv $ MkFunRoot keq (FragEQ b) $
        Frag.envFrag_inn fragEnv inner_fr{fragExt = ding_ext_inner ding'}
    setM $ reduced || derived
    pure $ OK (ding_derived ding',SimplClass $ singleton (k,c))
  where
  fragEnv = envPassThru env

  inner_ext = fragExt inner_fr
  (neg,pos) = flip foldMap (unExt inner_ext) $ \count ->
    if count < 0 then (invertSign count,0) else (0,count)
  ding = MkDeriving{
      ding_derived = emptyDerived
    ,
      ding_ext_inner = inner_ext
    ,
      ding_ext_outer = ext
    ,
      ding_neg = neg
    ,
      ding_pos = pos
    ,
      ding_tot = tot
    }
  mding' = loopDeriving env b ding

-----

data Deriving b = MkDeriving{
    ding_derived :: !(Derived b b)
  ,
    -- | First @...@ in @SetFrag (FragEQ b ('Nil ...) ...)@.
    ding_ext_inner :: !(Ext b)
  ,
    -- | Second @...@ in @SetFrag (FragEQ b ('Nil ...) ...)@.
    ding_ext_outer :: !(Ext b)
  ,
    -- | Total negative multiplicity of elements with negative multiplicity in 'ding_ext_inner'.
    ding_neg :: !Count
  ,
    -- | Total multiplicity of elements with positive multiplicity in 'ding_ext_inner'.
    ding_pos :: !Count
  ,
    -- | Total multiplicity of 'ding_ext_outer'.
    ding_tot :: !Count
  }

-- Something was derived IFF the internal neg and/or pos count decreased.
differentDeriving :: Deriving b -> Deriving b -> Bool
differentDeriving l r = changed1 ding_neg || changed1 ding_pos
  where
  changed1 f = f l /= f r

-- Loop if anything was derived, so that order of basis elements considered does not matter
loopDeriving :: Key b => Env k b r -> b -> Deriving b -> Contra (Deriving b)
loopDeriving env b ding = do
  ding' <- foldlExt (ding_ext_inner ding) (OK ding) $ \acc b' count -> acc >>= snocDeriving env b b' count
  if not (differentDeriving ding ding') then pure ding' else loopDeriving env b ding'

snocDeriving :: Key b => Env k b r -> b -> b -> Count -> Deriving b -> Contra (Deriving b)
snocDeriving env b b' count  acc
  | contra = Contradiction
  | mustneq || musteq = OK $ hit musteq
  | otherwise = OK acc
  where
  contra =   -- contradiction:
      -- SetFrag (FragEQ b ('Nil :- x) :- '())
      --   s.t. ding_tot = -1,ding_pos = 0
      (ding_tot acc + ding_pos acc < 0)
    ||
      -- SetFrag (FragEQ b ('Nil :+ x :- y) :+ '() :+ '() :+ '())
      --   s.t. ding_tot = 3,ding_neg = 1
      (1 < ding_tot acc - ding_neg acc)
    ||
      (musteq && mustneq)

  musteq =    -- derived ~:
      -- SetFrag (FragEQ b ('Nil :- x :- x :- y) :+ '() :+ '() :+ '())   to   (SetFrag (FragEQ b ('Nil :- y) :+ '()),b ~ x)
      --   s.t. ding_tot = 3,other_neg = 1
      (bneg && ding_tot acc - other_neg > 1)
    ||
      -- SetFrag (FragEQ b ('Nil :+ x :+ x :+ x :- y :- z) :- '())   to   (SetFrag (FragEQ b ('Nil :- y :- z) :+ '() :+ '()),b ~ x)
      --   s.t. ding_tot = -1,other_pos = 0
      (bpos && ding_tot acc + other_pos < 0)

  mustneq =    -- derived /~:
      -- SetFrag (FragEQ b ('Nil :- x))   to   (SetFrag (FragEQ b 'Nil),b /~ x)
      --   s.t. ding_tot = 0,count = -1,ding_pos = 0
      -- SetFrag (FragEQ b ('Nil :- x :- x :- x :+ y :+ z) :- '())   to   (SetFrag (FragEQ b ('Nil :+ y :+ z) :- '()),b /~ x)
      --   s.t. ding_tot = -1,count = -3,ding_pos = 2
      (bneg && ding_tot acc + count + ding_pos acc < 0)
    ||
      -- SetFrag (FragEQ b ('Nil :+ x) :+ '())   to   (SetFrag (FragEQ b 'Nil :+ '()),b /~ x)
      --   s.t. ding_tot = 1,count = 1,ding_neg = 0
      -- SetFrag (FragEQ b ('Nil :+ x :+ x :+ x :- y :- z) :+ '() :+ '())   to   (SetFrag (FragEQ b ('Nil :- y :- z) :+ '() :+ '()),b /~ x)
      --   s.t. ding_tot = 2,count = 3,ding_neg = 2
      (bpos && ding_tot acc + count - ding_neg acc > 1)

  bneg = count < 0
  bpos = count > 0
  abscount = abs count

  other_neg = let x = ding_neg acc in if bneg then x - abscount else x
  other_pos = let x = ding_pos acc in if bpos then x - abscount else x

  fragEnv = envPassThru env
  hit equal = MkDeriving{
      -- add
      ding_derived = let
        overlens = if equal then over lens_deqs else over lens_dneqs
        in
        insertFMS (b,b') () `overlens` ding_derived acc
    ,
      -- remove
      ding_ext_inner = insertExt b' (invertSign count) (ding_ext_inner acc)
    ,
      -- add if equal
      ding_ext_outer = (if equal then insertExt (Frag.envUnit fragEnv) count else id) (ding_ext_outer acc)
    ,
      -- remove if bneg
      ding_neg = other_neg
    ,
      -- remove if bpos
      ding_pos = other_pos
    ,
      -- add if equal
      ding_tot = (if equal then (+ count) else id) (ding_tot acc)
    }
