{-# LANGUAGE ConstraintKinds #-}   -- at least MonadFree
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies#-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}   -- at least Functor SumAt

{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}

{-# OPTIONS_GHC -fconstraint-solver-iterations=50 #-}

module Main where

import qualified Control.Monad.Except as MTL
import qualified Control.Monad.State as MTL
import qualified Control.Monad.Free as Free
import Data.Functor.Fun (type (~>)(..))
import Data.Implic
import Data.Motley

newtype SumAt (fs :: Frag (* -> *)) (a :: *) = MkSumAt{sumAt :: Sum fs (At a)}

instance Implic (Prod fs (Compose (Dict1 Eq) (At a))) => Eq (SumAt fs a) where
  MkSumAt c1 == MkSumAt c2 = c1 == c2

instance Show (Sum fs (At a)) => Show (SumAt fs a) where
  showsPrec p = showsPrec p . sumAt

instance Implic (Prod fs (Dict1 Functor)) => Functor (SumAt fs) where
  fmap = \f -> MkSumAt . updateSum (mapProd (g f) implic) . sumAt
    where
    g :: (a -> b) -> Dict1 Functor f -> (At a ~> At b) f
    g f MkDict1 = MkFun $ MkAt . fmap f . getAt

instance (Implic (Prod fs (Dict1 Foldable)),Implic (Prod fs (Dict1 Functor))) => Foldable (SumAt fs) where
  foldMap = \f -> foldMapSum getConst . updateSum (mapProd (g f) implic) . sumAt
    where
    g :: Monoid m => (a -> m) -> Dict1 Foldable f -> (At a ~> Const m) f
    g f MkDict1 = MkFun $ Const . foldMap f . getAt

instance (Implic (Prod fs (Dict1 Foldable)),Implic (Prod fs (Dict1 Functor)),Implic (Prod fs (Dict1 Traversable))) => Traversable (SumAt fs) where
  traverse = \f -> fmap MkSumAt . traverseSum getCompose . updateSum (mapProd (g f) implic) . sumAt
    where
    g :: Applicative i => (a -> i b) -> Dict1 Traversable f -> (At a ~> Compose i (At b)) f
    g f MkDict1 = MkFun $ Compose . fmap MkAt . traverse f . getAt

-----

type Free fs a = Free.Free (SumAt fs) a

type MonadFree fs = Free.MonadFree (SumAt fs)

wrap ::
    (
      MonadFree (fs :+ f) m
    ,
      ImplicProd (Dict1 Functor) (fs :+ f)
    ,
      KnownFragCard (FragLT f fs),FragEQ f fs ~ 'Nil
    )
  =>
    f (m a) -> m a
wrap = Free.wrap . MkSumAt . inj . MkAt

liftF ::
    (
      MonadFree (fs :+ f) m
    ,
      Functor f
    ,
      ImplicProd (Dict1 Functor) (fs :+ f)
    ,
      KnownFragCard (FragLT f fs),FragEQ f fs ~ 'Nil
    )
  =>
   f a -> m a
liftF = wrap . fmap pure

-----

newtype Error e a = MkError e
  deriving Functor via (Const e)

throwError ::
    (
      KnownFragCard (FragLT (Error e) fs)
    ,
      ImplicProd (Dict1 Functor) (fs :+ Error e)
    ,
      FragEQ (Error e) fs ~ 'Nil
    )
  =>
    e -> Free (fs :+ Error e) a
throwError = wrap . MkError

runError ::
  forall e fs a.
    (
      KnownFragCard (FragLT (Error e) fs)
    ,
      ImplicProd (Dict1 Functor) (fs :+ Error e)
    ,
      FragEQ (Error e) fs ~ 'Nil
    ,
      SetFrag (fs :+ Error e) ~ '()
    )
  =>
    Free (fs :+ Error e) a -> Free fs (Either e a)
runError = Free.iter phi . fmap (withImplicProd dicts2 pure . Right)
  where
  phi :: SumAt (fs :+ Error e) (Free fs (Either e a)) -> Free fs (Either e a)
  phi = alt (Free.Free . MkSumAt) f   .   sumAt

  f :: At (Free fs (Either e a)) (Error e) -> Free fs (Either e a)
  f = \(MkAt (MkError e)) -> withImplicProd dicts2 pure (Left e)

  dicts1 :: Imp (Prod (fs :+ Error e) (Dict1 Functor))
  dicts1 = implic

  dicts2 :: Imp (Prod fs (Dict1 Functor))
  dicts2 = pullImplicProd $ fst $ ret $ pushImplicProd dicts1

handleError ::
  forall e fs a.
    (
      KnownFragCard (FragLT (Error e) fs)
    ,
      ImplicProd (Dict1 Functor) (fs :+ Error e)
    ,
      FragEQ (Error e) fs ~ 'Nil
    ,
      SetFrag (fs :+ Error e) ~ '()
    )
  =>
    Free (fs :+ Error e) a -> (e -> Free fs a) -> Free fs a
handleError = \cop h -> withImplicProd dicts2 $ runError cop >>= \case
  Left e -> h e
  Right x -> pure x
  where
  dicts1 :: Imp (Prod (fs :+ Error e) (Dict1 Functor))
  dicts1 = implic

  dicts2 :: Imp (Prod fs (Dict1 Functor))
  dicts2 = pullImplicProd $ fst $ ret $ pushImplicProd dicts1

catchError ::
  forall e fs a.
    (
      KnownFragCard (FragLT (Error e) fs)
    ,
      ImplicProd (Dict1 Functor) (fs :+ Error e)
    ,
      FragEQ (Error e) fs ~ 'Nil
    ,
      SetFrag (fs :+ Error e) ~ '()
    )
  =>
    Free (fs :+ Error e) a -> (e -> Free (fs :+ Error e) a) -> Free (fs :+ Error e) a
catchError = \cop h -> weaken (runError cop) >>= \case
  Left e -> h e
  Right x -> pure x
  where
  weaken = Free.hoistFree $ MkSumAt . flip plusSum Proxy . sumAt

-----

data State s a =
    Get (s -> a)
  |
    Put !s a
instance Functor (State s) where
  fmap = \f -> \case
    Get k -> Get (f . k)
    Put s a -> Put s (f a)

get ::
    (
      KnownFragCard (FragLT (State s) fs)
    ,
      ImplicProd (Dict1 Functor) (fs :+ State s)
    ,
      FragEQ (State s) fs ~ 'Nil
    )
  =>
    Free (fs :+ State s) s
get = wrap $ Get pure

put ::
    (
      KnownFragCard (FragLT (State s) fs)
    ,
      ImplicProd (Dict1 Functor) (fs :+ State s)
    ,
      FragEQ (State s) fs ~ 'Nil
    )
  =>
    s -> Free (fs :+ State s) ()
put = \s -> wrap $ Put s (pure ())

runState ::
  forall s fs a.
    (
      KnownFragCard (FragLT (State s) fs)
    ,
      ImplicProd (Dict1 Functor) (fs :+ State s)
    ,
      FragEQ (State s) fs ~ 'Nil
    ,
      SetFrag (fs :+ State s) ~ '()
    )
  =>
    s -> Free (fs :+ State s) a -> Free fs (a,s)
runState = flip $ Free.iter phi . fmap (\a s -> withImplic dicts2 pure (a,s))
  where
  phi :: SumAt (fs :+ State s) (s -> Free fs (a,s)) -> s -> Free fs (a,s)
  phi = alt (\cop s -> Free.Free $ withImplic dicts2 fmap ($ s) $ MkSumAt cop) (f . getAt)   .   sumAt

  dicts1 :: Imp (Prod (fs :+ State s) (Dict1 Functor))
  dicts1 = implic

  dicts2 :: Imp (Prod fs (Dict1 Functor))
  dicts2 = pullImplicProd $ fst $ ret $ pushImplicProd dicts1

  f :: State s (s -> Free fs (a,s)) -> s -> Free fs (a,s)
  f = \case
    Get k -> \s -> k s s
    Put s a -> \_ -> a s

runFree :: Free 'Nil a -> a
runFree = \case
  Free.Pure a -> a
  Free.Free (MkSumAt cop) -> absurd "runFree" cop

-----

{-  causing solverloop
modify f = do
  x <- get
  put (f x)
  pure x
-}

main :: IO ()
main = do
  putStrLn "just state"
  putStrLn "((0,1,2),0) expected"
  print $ runFree $ runState (0 :: Int) $ do
    x0 <- get
    put $ x0 + 1
    x1 <- do
      x1 <- get
      put $ x1 + 1
      pure x1
    x2 <- get
    put $ x2 - 2
    pure (x0,x1,x2)

  putStrLn ""

  putStrLn "throwError; error around state"
  print $ runFree $ runError $ runState (0 :: Int) $ do
    x0 <- get
    put $ x0 + 1
    x1 <- do
      x1 <- get
      put $ x1 + 1
      pure x1
    _ <- throwError ()
    x2 <- get
    put $ x2 - 2
    pure (x0,x1,x2)

  putStrLn ""

  putStrLn "throwError; state around error"
  print $ runFree $ runState (0 :: Int) $ runError $ do
    x0 <- get
    put $ x0 + 1
    x1 <- do
      x1 <- get
      put $ x1 + 1
      pure x1
    _ <- throwError ()
    x2 <- get
    put $ x2 - 2
    pure (x0,x1,x2)

  putStrLn ""

  putStrLn "handleError"
  print $ runFree $ runState (0 :: Int) $ do
    x0 <- get
    put $ x0 + 1
    flip handleError (\_ -> pure ()) $ do
      do
        x1 <- get
        put $ x1 + 1
      _ <- throwError ()
      x2 <- get
      put $ x2 - 2
      pure ()

  putStrLn ""

  putStrLn "catchError; state around error"
  print $ runFree $ runState (0 :: Int) $ runError $ do
    x0 <- get
    put $ x0 + 1
    flip catchError (\_ -> pure ()) $ do
      do
        x1 <- get
        put $ x1 + 1
      _ <- throwError ()
      x2 <- get
      put $ x2 - 2
      pure ()

  putStrLn ""

  putStrLn "catchError; error around state"
  print $ runFree $ runError $ runState (0 :: Int) $ do
    x0 <- get
    put $ x0 + 1
    flip catchError (\_ -> pure ()) $ do
      do
        x1 <- get
        put $ x1 + 1
      _ <- throwError ()
      x2 <- get
      put $ x2 - 2
      pure ()

  putStrLn ""
  putStrLn "===================="
  putStrLn ""

  putStrLn "MTL just state"
  putStrLn "((0,1,2),0) expected"
  print $ flip MTL.runState (0 :: Int) $ do
    x0 <- MTL.get
    MTL.put $ x0 + 1
    x1 <- do
      x1 <- MTL.get
      MTL.put $ x1 + 1
      pure x1
    x2 <- MTL.get
    MTL.put $ x2 - 2
    pure (x0,x1,x2)

  putStrLn ""

  putStrLn "MTL throwError; error around state"
  print $ MTL.runExcept $ flip MTL.runStateT (0 :: Int) $ do
    x0 <- MTL.get
    MTL.put $ x0 + 1
    x1 <- do
      x1 <- MTL.get
      MTL.put $ x1 + 1
      pure x1
    _ <- MTL.throwError ()
    x2 <- MTL.get
    MTL.put $ x2 - 2
    pure (x0,x1,x2)

  putStrLn ""

  putStrLn "MTL throwError; state around error"
  print $ flip MTL.runState (0 :: Int) $ MTL.runExceptT $ do
    x0 <- MTL.get
    MTL.put $ x0 + 1
    x1 <- do
      x1 <- MTL.get
      MTL.put $ x1 + 1
      pure x1
    _ <- MTL.throwError ()
    x2 <- MTL.get
    MTL.put $ x2 - 2
    pure (x0,x1,x2)

  putStrLn ""

  putStrLn "MTL catchError; state around error"
  print $ flip MTL.runState (0 :: Int) $ MTL.runExceptT $ do
    x0 <- MTL.get
    MTL.put $ x0 + 1
    flip MTL.catchError (\_ -> pure ()) $ do
      do
        x1 <- MTL.get
        MTL.put $ x1 + 1
      _ <- MTL.throwError ()
      x2 <- MTL.get
      MTL.put $ x2 - 2
      pure ()

  putStrLn ""

  putStrLn "MTL catchError; error around state"
  print $ MTL.runExcept $ flip MTL.runStateT (0 :: Int) $ do
    x0 <- MTL.get
    MTL.put $ x0 + 1
    flip MTL.catchError (\_ -> pure ()) $ do
      do
        x1 <- MTL.get
        MTL.put $ x1 + 1
      _ <- MTL.throwError ()
      x2 <- MTL.get
      MTL.put $ x2 - 2
      pure ()
