{-# LANGUAGE Arrows #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -dcore-lint -fplugin=Data.Frag.Plugin #-}

{-# OPTIONS_GHC -Wall -Werror #-}
{-# OPTIONS_GHC -Wwarn=missing-signatures #-}

module Main where

import Control.Arrow (Arrow,ArrowApply,returnA)
import Data.Frag
import Data.Motley

extRoute_Arrow :: (
    FragEQ a p ~ 'Nil
  ,
    KnownFragCard (FragLT a p)
  ,
    FragEQ a q ~ 'Nil
  ,
    KnownFragCard (FragLT a q)
  ,
    Arrow arr
  )
  =>
    arr (Prod p f) (Prod q g)
  ->
    arr (f a) (g a)
  ->
    arr (Prod (p :+ a) f) (Prod (q :+ a) g)
extRoute_Arrow = \r k -> proc fsf -> do
  let
    (fs,f) = ret fsf
  gs <- r -< fs
  g <- k -< f
  returnA -< ext gs g

extRouteWith_Arrow :: (
    FragEQ a p ~ 'Nil
  ,
    KnownFragCard (FragLT a p)
  ,
    FragEQ a q ~ 'Nil
  ,
    KnownFragCard (FragLT a q)
  ,
    ArrowApply arr
  )
  =>
    arr (Prod p f) (Prod q g)
  ->
    (Prod q g -> arr (f a) (g a))
  ->
    arr (Prod (p :+ a) f) (Prod (q :+ a) g)
extRouteWith_Arrow = \r k -> proc fsf -> do
  let
    (fs,f) = ret fsf
  gs <- r -< fs
  g <- k gs -<< f   -- NB -<< uses ArrowApply
  returnA -< ext gs g

-----

-- | A traversal that visits each factor exactly once in a fixed order.
-- Each visit consists of a request,
-- which the expected given handler will convert to a response.
-- Both requests and replies may depend on the factor's pre-existing \"environment\" value.
-- A request may additionally depend on the replies from previously visited factors.
newtype Route env req m p rsp = MkRoute{
    runRoute ::
        (forall a. env a -> req a -> m (rsp a))
        -- ^ request handler
      ->
        Prod p env
        -- ^ incoming environment
      ->
        m (Prod p rsp)
  }

nilRoute :: Applicative m => Route env req m 'Nil rsp
nilRoute = MkRoute $ \_ _ -> pure nil

extRoute ::
    (
      FragEQ a p ~ 'Nil
    ,
      KnownFragCard (FragLT a p)
    ,
      Monad m
    )
  =>
    (env a -> req a)
  ->
    (env a -> rsp a -> Route env req m p rsp)
  ->
    Route env req m (p :+ a) rsp
extRoute = \mkReq k -> MkRoute $ \visit envsenv -> do
  let
    (envs,env) = ret envsenv
    req = mkReq env
  rsp <- visit env req
  flip ext rsp <$> runRoute (k env rsp) visit envs

test () =
  extRoute (id' (Proxy :: Proxy 3)) $ \_ _ ->
  extRoute (id' (Proxy :: Proxy 1)) $ \_ _ ->
  nilRoute
  where
  id' :: proxy a -> env a -> U1 a
  id' = \_ _ -> U1

main :: IO ()
main = do
  ls <- runRoute
    (test ())
    (\(Const s) U1 -> Const (length s) <$ putStrLn s)
    (nil `ext` (Const "1" :: Const String 1) `ext` Const "three")
  print ls
  pure ()
