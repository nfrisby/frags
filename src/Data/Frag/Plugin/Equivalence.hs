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
  -- interpret each raw side
  --
  -- NB It's important that the roots are not unnecessarily unflattened.
  --
  -- > fmap envFunRoot_inn . envFunRoot_out /= pure
  --
  -- because it may start as a fsk,
  -- and we don't expect 'envFunRoot_inn' to reflatten.
  --
  -- It's important it remain a fsk for the sake of 'envNeedSwap'.
  let
    f = Frag.reinterpret (envPassThru env)
  printM $ O.text "ENTER reinterpret Equivalence"
  (hit,(lfr,rfr)) <- listeningM $ (,) <$> f l <*> f r
  printM $ O.text "EXIT reinterpret Equivalence" O.<+> O.ppr hit

  -- x :+ a ~ y :+ b   no swap, transferred   x ~ y :- a :+ b
  -- y :+ b ~ x :+ a   swap, transferred   x ~ y :- a :+ b
  -- x ~ y :- a :+ b   no swap, no transferred
  -- y :- a :+ b ~ x   swap, transferred   x ~ y :- a :+ b

  -- 'Nil ~ x :+ a   swap, transferred   x ~ 'Nil :- a
  -- x :+ a ~ 'Nil   no swap, transferred   x ~ 'Nil :- a
  -- x ~ 'Nil :- a   no swap, no transferred
  -- 'Nil :- a ~ x   swap, no transferred   x ~ 'Nil :- a

  -- 'Nil :- a ~ 'Nil   no swap, no transferred   'Nil ~ 'Nil :- a

  -- swap roots if needed
  let
    -- swapped: 'Nil ~ x   to   x ~ 'Nil
    swapped = envNeedSwap env (fragRoot lfr) (fragRoot rfr)

    (lfr',rfr')
      | swapped = (rfr,lfr)
      | otherwise = (lfr,rfr)

  printM $ O.text "swapped" O.<+> O.ppr swapped O.<+> Frag.envShow (envPassThru env) (O.ppr (fragRoot lfr,fragRoot rfr))

  let
    lr = fragRoot lfr'
    rr = fragRoot rfr'

    nilnil = Frag.envIsNil fragEnv lr && Frag.envIsNil fragEnv rr
      where
      fragEnv = envPassThru env

  -- NB We do not call @setM swapped@.
  --
  -- If we were to swap @(y :+ b) ~ x@ to @x ~ (y :+ b)@,
  -- then GHC may swap it back, which would cause an infinite loop.
  -- The subtlety is that @y :+ b@ will flatten to a fsk,
  -- and that fsk may be cached and have a deeper level than does @x@.
  --
  -- TODO Do @setM swapped@ if this equivalence occurs as subterm, not as a Given/Wanted

  -- move any extension on the left over to the right
  let
    lext = fragExt lfr'
    rext = fragExt rfr'
    lext_empty = nullFM (unExt lext)
    rext_empty = nullFM (unExt rext)

    (transferred,ext)
      | nilnil && not lext_empty && rext_empty = (False,lext)
      | otherwise = (not lext_empty && not rext_empty,rext `subtractExt` lext)

  setM transferred
  when transferred $ printM $ Frag.envShow (envPassThru env) $ O.text "transferred" O.$$ O.ppr lfr' O.$$ O.ppr rfr' O.$$ O.ppr ext

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
