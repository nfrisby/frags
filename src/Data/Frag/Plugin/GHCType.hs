{-# LANGUAGE PatternGuards #-}

module Data.Frag.Plugin.GHCType (
  fragEquivalence_candidate_out,
  funRoot_out,
  knownFragZ_out,
  rawFrag_out,
  setFrag_out,
  ) where

import Class (classTyCon)
import DataCon (promoteDataCon)
import TcType (TcKind,TcType,tcSplitTyConApp_maybe,typeKind)
import TcRnTypes (Ct(..),ctPred)
import Type (EqRel(NomEq),PredTree(ClassPred,EqPred),classifyPredType)
import TysWiredIn (unitDataCon)

import Data.Frag.Plugin.GHCType.Fsk (Unflat,unflatten)
import Data.Frag.Plugin.Lookups (E(..))
import Data.Frag.Plugin.Types

rawFrag_out :: E -> Unflat -> TcType -> RawFrag TcType TcType
rawFrag_out env unflat = go id
  where
  go acc = go2 acc . unflatten unflat

  go2 acc = \ty -> case tcSplitTyConApp_maybe ty of
    Just (tc,[_,fr,b])
      | tc == fragMinusTC env -> go (\x -> ExtRawExt (acc x) Neg b) fr
      | tc == fragPlusTC env -> go (\x -> ExtRawExt (acc x) Pos b) fr

    _ -> MkRawFrag (acc NilRawExt) ty

funRoot_out :: E -> Unflat -> TcType -> Maybe (FunRoot TcKind TcType TcType)
funRoot_out env unflat = \ty -> case tcSplitTyConApp_maybe (unflatten unflat ty) of
  Just (tc,k:args) -> let
    mk x y = Just $ MkFunRoot k x y
    in case args of
    [fr]
      | tc == fragCardTC env -> mk FragCard fr
    [b,fr]
      | tc == fragEQTC env -> mk (FragEQ b) fr
      | tc == fragLTTC env -> mk (FragLT b) fr
      | tc == fragNETC env -> mk (FragNE b) fr
    _ -> Nothing
  _ -> Nothing

-- | @(k,l,r)@ in @l ~ r :: Frag k@
fragEquivalence_candidate_out :: E -> Ct -> Maybe (TcKind,TcType,TcType)
fragEquivalence_candidate_out env ct = case classifyPredType (ctPred ct) of
  EqPred NomEq l r
    | Just (tc,[k]) <- tcSplitTyConApp_maybe (typeKind l)
    , tc == fragTC env -> Just (k,l,r)
  _ -> Nothing

-- | @(k,fr)@ in @SetFrag (fr :: Frag k) ~ '()@
setFrag_out :: E -> Unflat -> Ct -> Maybe (TcKind,TcType)
setFrag_out env unflat ct = case classifyPredType (ctPred ct) of
  EqPred NomEq l r
    | Just (tc,[]) <- tcSplitTyConApp_maybe r
    , tc == promoteDataCon unitDataCon
    , Just (tc2,[k,fr]) <- tcSplitTyConApp_maybe (unflatten unflat l)
    , tc2 == setFragTC env -> Just (k,fr)
  _ -> Nothing

-- | @(k,fr)@ in @KnownFragCard (fr :: Frag k)@
knownFragZ_out :: E -> Ct -> Maybe (TcKind,TcType)
knownFragZ_out env ct = case classifyPredType (ctPred ct) of
  ClassPred cls [k,fr]
    | classTyCon cls == knownFragZTC env -> Just (k,fr)
  _ -> Nothing
