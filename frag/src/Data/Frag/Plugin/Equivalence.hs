{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}

module Data.Frag.Plugin.Equivalence (
  Env(..),
  interpret,
  simplify,
  ) where

import Control.Monad (when)
import Data.Monoid (First(..))
import qualified Outputable as O

import qualified Data.Frag.Plugin.Equivalence.FragEQNil as FragEQNil
import qualified Data.Frag.Plugin.Equivalence.NilNil as NilNil
import qualified Data.Frag.Plugin.Frag as Frag
import Data.Frag.Plugin.Types

data Env k b r = MkEnv{
    -- | /Definitely/ equal
    envEqR :: !(r -> r -> Bool)
  ,
    -- | The semantics of @r@ can prefer which root be on the left.
    envNeedSwap :: !(r -> r -> Bool)
  ,
    -- | Are not definitely apart. 
    envNotApart :: !(b -> b -> Bool)
  ,
    envMultiplicity :: !(r -> b -> Maybe CountInterval)
  ,
    -- | See 'Data.Frag.Plugin.Frag.Env'.
    envPassThru :: Frag.Env k b r
  }

interpret :: (Key b,Monad m) => Env k b r -> RawFragEquivalence b r -> AnyT m (FragEquivalence b r)
interpret env (MkRawFragEquivalence l r) = do
  let
    fragEnv = envPassThru env
    f = Frag.reinterpret fragEnv
  printM $ O.text "reinterpret Equivalence {"
  (hit,(lfr,rfr)) <- listeningM $ (,) <$> f l <*> f r
  printM $ O.text "reinterpret Equivalence }" O.<+> O.ppr hit

  -- step 1: prioritize left root
  let
    mustSwap = envNeedSwap env (fragRoot lfr) (fragRoot rfr)
    mustNotSwap = envNeedSwap env (fragRoot rfr) (fragRoot lfr)

    (lfr',rfr')
      | mustSwap = (rfr,lfr)
      | otherwise = (lfr,rfr)
    lr = fragRoot lfr'
    rr = fragRoot rfr'
    lext = fragExt lfr'
    rext = fragExt rfr'

  printM $ O.text "mustSwap" O.<+> O.ppr mustSwap O.<+> Frag.envShow (envPassThru env) (O.ppr (fragRoot lfr,fragRoot rfr))

  -- step 2: collect tallies on right side
  let
    lnil = Frag.envIsNil fragEnv lr
    rnil = Frag.envIsNil fragEnv rr
    nilnil = lnil && rnil

    lemp = nullFM (unExt lext)
    remp = nullFM (unExt rext)

    (transferred,ext)
      | lemp = (False,rext)
        -- ('Nil :- 1) ~ 'Nil   to   'Nil ~ ('Nil :- 1)
      | lnil && rnil && remp = (False,lext)   -- NB moved w/o subtraction
      | otherwise = (flag,rext `subtractExt` lext)
      where
      flag =   -- NB context includes not lemp
          -- (_ :+ 1) ~ (_ :+ 2)   to   _ ~ (_ :- 1 :+ 2)
          (not remp)
        ||
          -- (tau[3] :+ Int) ~ skolem[1]   to   tau[3] ~ (skolem[1] :- Int)
          mustNotSwap   -- NB crucial for some unifications

  setM transferred
  when transferred $ printM $ Frag.envShow (envPassThru env) $ O.text "transferred" O.$$ O.ppr lfr' O.$$ O.ppr rfr' O.$$ O.ppr ext

  -- step 3: polarize the extension if roots are both 'Nil
  ext' <- if nilnil then polarize env ext else pure ext

  pure $ MkFragEquivalence lr rr ext'

polarize :: (Key b,Monad m) => Env k b r -> Ext b -> AnyT m (Ext b)
polarize env ext = do
  let
    -- inverted: 'Nil ~ 'Nil :- a :+ b   to   'Nil ~ 'Nil :+ a :- b
    inverted = maybe False id $ getFirst $ flip foldMap (unExt ext) $ \count ->
      First $ if 0 == count then Nothing else Just (count < 0)

    ext' = if inverted then invertSign ext else ext

  when inverted $ printM $ Frag.envShow (envPassThru env) $ O.text "inverted" O.<+> O.ppr ext O.<+> O.ppr ext'
  setM inverted

  pure ext'

reinterpret :: (Key b,Monad m) => Env k b r -> FragEquivalence b r -> AnyT m (FragEquivalence b r)
reinterpret env (MkFragEquivalence l r ext) = interpret env $ MkRawFragEquivalence (MkFrag emptyExt l) (MkFrag ext r)

-----

isFragEQ :: Env k b r -> r -> Maybe (k,b,r)
isFragEQ env r = case Frag.envFunRoot_out (envPassThru env) r of
  Nothing -> Nothing
  Just (MkFunRoot keq fun arg) -> case fun of
    FragEQ b -> Just (keq,b,arg)
    _ -> Nothing

simplify :: (Key b,Monad m) => Env k b r -> k -> FragEquivalence b r -> AnyT m (Contra (Derived b b,FragEquivalence b r))
simplify env knd freq = reinterpret env freq >>= simplify_ env knd

simplify_ :: (Key b,Monad m) => Env k b r -> k -> FragEquivalence b r -> AnyT m (Contra (Derived b b,FragEquivalence b r))
simplify_ env knd eq0@(MkFragEquivalence l r ext)
  | not (Frag.envIsNil fragEnv l) && envEqR env l r = do
    -- cancel_roots: x ~ x ...   to    'Nil ~ 'Nil ...
    setM True
    simplify env knd $ MkFragEquivalence (Frag.envNil fragEnv knd) (Frag.envNil fragEnv knd) ext

  | Frag.envIsNil fragEnv l && Frag.envIsNil fragEnv r = do
    case NilNil.simplify notApart ext of
      Nothing -> preferM (stuck__ eq0) $ stuck_ (MkFragEquivalence l r ext)
      Just x -> do
        setM True
        flip mapM x $ \(derived,ext') -> do
          ext'' <- polarize env ext'
          pure (derived,MkFragEquivalence l r ext'')
  | Just (keq,b,arg) <- isFragEQ env l, Frag.envIsNil fragEnv r = do
    (was_not_canonical,fr) <- hypotheticallyM $ Frag.interpret fragEnv arg
    when was_not_canonical $ fail "simplifyEquivalence FragEQ argument was incompletely interpreted"

    let
      eq_ext = fragExt fr
      eq_root = fragRoot fr
    
    let
      intrvl = MkCountInterval{
          atLeast = k - pcount
        ,
          atMost = k + ncount
        }
        where
        MkNegPosExt _ ncount _ pcount = splitExt eq_ext
        k = foldMap id (unExt ext)

    if
      | Frag.envIsNil fragEnv eq_root
      , Just x <- FragEQNil.simplify notApart b eq_ext ext -> do
        setM True
        pure $ (\derived -> (derived,MkFragEquivalence (Frag.envNil fragEnv (Frag.envZBasis fragEnv)) r emptyExt)) <$> x

      -- contradiction: if 0 <= eq_root(b) <= 2 then FragEQ b (x :+ _ :- _) cannot be 5
      | Just intrvl' <- envMultiplicity env eq_root b
      , emptyInterval (intrvl <> intrvl') -> do setM True; pure Contradiction

      | otherwise -> stuck_ $ MkFragEquivalence
        (Frag.envFunRoot_inn fragEnv $ MkFunRoot keq (FragEQ b)
           (Frag.envFrag_inn fragEnv $ MkFrag eq_ext eq_root))
        r ext
  | otherwise = stuck
  where
  fragEnv = envPassThru env

  stuck__ x = OK (emptyDerived,x)
  stuck_ x = pure (stuck__ x)
  stuck = stuck_ eq0

  notApart x y = envNotApart env x y
