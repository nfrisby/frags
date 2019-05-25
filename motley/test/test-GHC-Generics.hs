{-# OPTIONS_GHC -dcore-lint #-}
{-# OPTIONS_GHC -fplugin=Data.Frag.Plugin #-}

module Main where

import Data.Motley.GHC.Generics
import GHC.Generics (Generic,Rep,from,to)

toRep :: Generic a => a -> Rep a x
toRep = from

fromRep :: Generic a => Rep a x -> a
fromRep = to

main :: IO ()
main = do
  print $ toSum $ toRep (Just 'c')
  print $ toSum $ toRep (Nothing :: Maybe Char)
  print $ toSum $ toRep ()
  print $ toSum $ toRep (True,"foo")
  print $ toSum $ toRep ("foo",True)

--  print $ toProd $ toRep (Just 'c')   -- no instance for :+:
  print $ toProd $ toRep ()
  print $ toProd $ toRep (True,"foo")
  print $ toProd $ toRep ("foo",True)

  print $ asTypeOf (fromRep . fromSum . toSum . toRep) id $ (Just 'c')
  print $ asTypeOf (fromRep . fromSum . toSum . toRep) id $ (Nothing :: Maybe Char)
  print $ asTypeOf (fromRep . fromSum . toSum . toRep) id $ ()
  print $ asTypeOf (fromRep . fromSum . toSum . toRep) id $ (True,"foo")
  print $ asTypeOf (fromRep . fromSum . toSum . toRep) id $ ("foo",True)

  print $ asTypeOf (fromRep . fromProd . toProd . toRep) id $ ()
  print $ asTypeOf (fromRep . fromProd . toProd . toRep) id $ (True,"foo")
  print $ asTypeOf (fromRep . fromProd . toProd . toRep) id $ ("foo",True)
