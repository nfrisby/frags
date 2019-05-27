{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=50 #-}

module Main where

import Data.Functor.Const (Const(..))
import FragTest

main :: IO ()
main = pure ()

-----

{-

As of 2d5d9003953609b51b25c39642285d44d4b86b6e, I see this instead of a useful error message.

app/Main-eff.hs:1:1: error:
    solveSimpleWanteds: too many iterations (limit = 4)
      Set limit with -fconstraint-solver-iterations=n; n=0 for no limit
      Simples = {[WD] $dMonadFree_awm4 {0}:: MonadFree
                                               (fs0 :+ f0) m0 (CNonCanonical),
                 [WD] $dImplicProd__awm5 {0}:: ImplicProd
                                                 (Dict1 Functor) (fs0 :+ f0) (CNonCanonical),
                 [WD] $dKnownFragCard_awm6 {0}:: KnownFragCard
                                                   (FragLT f0 fs0) (CNonCanonical),
                 [WD] $d~_awm7 {0}:: FragEQ f0 fs0 ~ 'Nil (CNonCanonical)}
      WC = WC {wc_simple =
                 [D] _ {0}:: 'Nil ~ 'Nil (CNonCanonical)
                 [WD] $dImplicProd__awyH {0}:: Data.Motley.ImplicProd_
                                                 (Dict1 Functor)
                                                 (Data.Frag.FragPop_NonDet
                                                    ((fs :- Error e) :+ Error e)) (CDictCan)
                 [W] $dMonadFree_awyI {0}:: Free.MonadFree
                                              (SumAt ((fs :- Error e) :+ Error e))
                                              (Free.Free (SumAt fs)) (CDictCan(psc))
                 [WD] $dKnownFragCard_awyL {0}:: KnownFragCard
                                                   (FragLT (Error e) (fs :- Error e)) (CDictCan)
                 [WD] hole{co_awyA} {5}:: FragEQ (Error e) (fs :- Error e)
                                          ~ 'Nil (CNonCanonical)
                 [D] _ {0}:: Data.Frag.FragPop_NonDet fs
                             ~ Data.Frag.FragPop_NonDet
                                 ((fs :- Error e) :+ Error e) (CNonCanonical)
-}

class MonadFree (fs :: Frag (* -> *)) (m :: * -> *) | m -> fs
instance MonadFree fs (Free fs)

data Free (fs :: Frag (* -> *)) (a :: *) = MkFree

wrap ::
    (
      MonadFree (fs :+ f) m
    ,
      KnownFragCard (FragLT f fs),FragEQ f fs ~ 'Nil
    )
  =>
    f (m a) -> m a
wrap = undefined

throwError ::
    (
      KnownFragCard (FragLT (Const e) fs)
    ,
      FragEQ (Const e) fs ~ 'Nil
    )
  =>
    e -> Free fs a
--    e -> Free (fs :+ Const e) a     -- this is bug-free
throwError = wrap . Const
