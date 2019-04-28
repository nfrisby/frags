{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}

module Data.Frag.Plugin.GHCType.Fsk (
  Unflat(..),
  collate_fsks,
  unflatten,
  ) where

import Data.Either (partitionEithers)
import qualified Digraph
import qualified Outputable as O
import TcType (TcType,TcTyVar,isFlattenTyVar)
import TcRnTypes (Ct(..),CtEvidence,Xi)
import TyCon (TyCon)
import Type (getTyVar_maybe,mkTyConApp)
import qualified UniqFM as UFM
import qualified UniqSet as USet

import Data.Frag.Plugin.Lookups (E(..))

-- | 'cc_ctev','cc_fun','cc_tyargs','cc_fsk'
type FunEq = (CtEvidence,TyCon,[Xi],TcTyVar)

getFunEq_maybe :: Ct -> Maybe FunEq
getFunEq_maybe = \case
  CFunEqCan a b c d -> Just (a,b,c,d)
  _ -> Nothing

data Alias = MkAlias !Ct !TcTyVar !TcTyVar

-- | @(fskL,fskR)@ from @fskL ~ fskR (CTyEqCan)@ if there is no @_ ~ fskL (CFunEqCan)@
getAlias_maybe :: USet.UniqSet TcTyVar -> Ct -> Maybe Alias
getAlias_maybe funeq_fsks = \case
  ct@CTyEqCan{cc_tyvar = fskL,cc_rhs = r}
    | Just fskR <- getTyVar_maybe r
    , isFlattenTyVar fskR
    , not (USet.elementOfUniqSet fskL funeq_fsks) -> Just $ MkAlias ct fskL fskR
  _ -> Nothing

-----

data FragFunEq =
    MkApartFunEq !TcTyVar !TcType
  |
    MkFragFunEq !TcTyVar TcType !(TcType -> TcType)

-- | @(fsk,fr,f)@ from @t ~ fsk (CFunEqCan)@ such that @(f fr)@ yields @t@.
getFragFunEq_maybe :: E -> FunEq -> Maybe FragFunEq
getFragFunEq_maybe env = \case
  (_,tc,[arg],fsk)
    | tc == apartTC env -> Just $ MkApartFunEq fsk (tc `mkTyConApp` [arg])
  (_,tc,k:args,fsk) -> case args of
    [fr]
      | tc == fragCardTC env -> f fr pure
      | tc == setFragTC env -> f fr pure
    [fr,b]
      | tc == fragMinusTC env -> f fr (\x -> [x,b])
      | tc == fragPlusTC env -> f fr (\x -> [x,b])
    [b,fr]
      | tc == fragEQTC env -> f fr (\x -> [b,x])
      | tc == fragLTTC env -> f fr (\x -> [b,x])
      | tc == fragNETC env -> f fr (\x -> [b,x])
    _ -> Nothing
    where
    f x inn = Just $ MkFragFunEq fsk x (mkTyConApp tc . (k:) . inn)
    
  _ -> Nothing

-----

-- | Fully flattens any fsk involving "Data.Frag" family applications.
newtype Unflat = MkUnflat{forgetUnflat :: UFM.UniqFM TcType}
  deriving (O.Outputable)

-- | Replace a frag-fsk by its 'Unflat' image.
--
-- Note: Acts as the identity function
-- if the argument is not itself a frag-fsk;
-- there is no recursion /etc/.
unflatten :: Unflat -> TcType -> TcType
unflatten (MkUnflat unflat) ty
  | Just fsk <- getTyVar_maybe ty
  , isFlattenTyVar fsk
  , Just ty' <- UFM.lookupUFM unflat fsk = ty'
  | otherwise = ty

-- | \"Consume\" relevant CFunEqCan and CTyEqCan Givens to create the corresponding 'Unflat'.
--
-- * A CFunEqCan is consumed if its LHS applies a "Data.Frag" type family.
-- * A CTyEqCan is consumed if its LHS is a fsk with no CFunEqCan and its RHS is a fsk owned by a consumed constraint.
collate_fsks :: E -> [Ct] -> (Unflat,[Ct])
collate_fsks env gs = (MkUnflat unflat,gs4)
  where
  -- partition out all funeqs
  (funeqs,gs1) = partitionMaybes getFunEq_maybe gs
  -- partition out all aliases (as determined by all funeqs);
  -- pass-through each given that is neither a funeq nor an alias
  (aliases,gs2) = partitionMaybes (getAlias_maybe funeq_fsks) gs1
    where
    funeq_fsks = USet.mkUniqSet [fsk | (_,_,_,fsk) <- funeqs]
  -- also pass-through funeqs that are not frag-relevant
  (frag_funeqs,passthru_funeqs) = partitionMaybes (getFragFunEq_maybe env) funeqs
  -- dependency-sort frag-funeqs and all aliases
  topo_fsk =
    map Digraph.node_payload $
    Digraph.topologicalSortG $
    Digraph.graphFromEdgedVerticesUniq $ [
      Digraph.DigraphNode (Right frfuneq) fsk $ case getTyVar_maybe fr of
        Just tv -> [tv]
        Nothing -> []
    | frfuneq@(MkFragFunEq fsk fr _) <- frag_funeqs
    ] ++ [
      Digraph.DigraphNode (Right frfuneq) fsk []
    | frfuneq@(MkApartFunEq fsk _) <- frag_funeqs
    ] ++ [
      Digraph.DigraphNode (Left alias) fskL [fskR]
    | alias@(MkAlias _ fskL fskR) <- aliases
    ]
  -- consume frag-funeqs and frag-aliases to build unflat;
  -- also pass-through non-frag aliases
  (unflat,gs3) = foldl (uncurry snoc) (UFM.emptyUFM,gs2) (reverse topo_fsk)
    where
    snoc acc1 acc2 = \case
      Left (MkAlias g fskL fskR) -> case UFM.lookupUFM acc1 fskR of
        Just fr -> (UFM.addToUFM acc1 fskL fr,acc2)   -- frag-alias
        Nothing -> (acc1,g:acc2)   -- non-frag alias
      Right (MkApartFunEq fsk arg) ->
        (UFM.addToUFM acc1 fsk arg,acc2)
      Right (MkFragFunEq fsk fr inn) ->
        (UFM.addToUFM acc1 fsk $ inn (unflatten (MkUnflat acc1) fr),acc2)
  gs4 = map (uncurry4 CFunEqCan) passthru_funeqs ++ gs3

partitionMaybes :: (a -> Maybe b) -> [a] -> ([b],[a])
partitionMaybes f as = partitionEithers [ maybe (Right a) Left (f a) | a <- as ]

uncurry4 :: (a -> b -> c -> d -> res) -> (a,b,c,d) -> res
uncurry4 fun (a,b,c,d) = fun a b c d
