{-# LANGUAGE LambdaCase #-}

-- |
module Data.Frag.Plugin.Lookups where

import CoAxiom (CoAxiom,Unbranched)
import GhcPlugins
import Outputable (SDoc)
import TcPluginM

import qualified GHC.TcPluginM.Extra as Extra

-- | The environment for 'Data.Frag.Plugin.plugin'.
data E = MkE{
    -- | @DynFlags@ as of plugin initialization
    dynFlags0 :: !DynFlags
  ,
    -- | @DynFlags@ as of plugin initialization
    piTrace :: !(SDoc -> TcPluginM ())
  ,

    -- | @Apart@ class
    apartTC :: !TyCon
  ,
    -- | @ConsApart@ DataCon
    apartConsDC :: !DataCon
  ,
    -- | @OneApart@ DataCon
    apartOneDC :: !DataCon
  ,

    -- | @Frag@ data type
    fragTC :: !TyCon
  ,
    -- | @Nil@ data constructor
    fragNilDC :: !DataCon
  ,
    -- | @:-@ type family
    fragMinusTC :: !TyCon
  ,
    -- | @:+@ type family
    fragPlusTC :: !TyCon
  ,

    -- | @FragCard@ type family
    fragCardTC :: !TyCon
  ,
    -- | @FragEQ@ type family
    fragEQTC :: !TyCon
  ,
    -- | @FragLT@ type family
    fragLTTC :: !TyCon
  ,
    -- | @FragNE@ type family
    fragNETC :: !TyCon
  ,

    -- | @KnownFragCard@ type family
    knownFragZTC :: !TyCon
  ,
    -- | @SetFrag@ type family
    setFragTC :: !TyCon
  ,

    knownFragZCoax :: !(CoAxiom Unbranched)
  ,
    -- | Implementation detail
    unsafeConvertProxyIntId :: !Id
  ,
    -- | Implementation detail
    unsafeProxyIntId :: !Id
  }

-----

-- |
lookups :: Bool -> TcPluginM E
lookups tracing = do
  dflags <- unsafeTcPluginTcM getDynFlags

  md <- do
    let
      myModule  = mkModuleName "Data.Frag"
      myPackage = fsLit "frag"
    Extra.lookupModule myModule myPackage

  let
    tyCon s = tcLookupTyCon =<< Extra.lookupName md (mkTcOcc s)

    dataCon tc s = case [ dc | dc <- tyConDataCons tc, occNameFS (occName (dataConName dc)) == fsLit s ] of
      [d] -> pure d
      _ -> panic $ "Data.Frag.Plugin initialization could not find DataCon " ++ s

    func s = Extra.lookupName md (mkVarOcc s) >>= tcLookupGlobal >>= \case
      AnId i -> pure i
      _ -> panic $ "Data.Frag.Plugin initialization could not find Id " ++ s

  ucpi <- func "unsafeConvertProxyInt"
  upi <- func "unsafeProxyInt"

  apart_TC <- tyCon "Apart"
  apartPairs_TC <- tyCon "ApartPairs"
  apartCons_DC <- dataCon apartPairs_TC "ConsApart"
  apartOne_DC <- dataCon apartPairs_TC "OneApart"

  frag_TC <- tyCon "Frag"
  fragNil_DC <- dataCon frag_TC "Nil"
  fragMinus_TC <- tyCon ":-"
  fragPlus_TC <- tyCon ":+"

  fragCard_TC <- tyCon "FragCard"
  fragEQ_TC <- tyCon "FragEQ"
  fragLT_TC <- tyCon "FragLT"
  fragNE_TC <- tyCon "FragNE"

  knownFragZ_TC <- tyCon "KnownFragCard"
  setFrag_TC <- tyCon "SetFrag"

  knownFragZ_Coax <- case newTyConCo_maybe knownFragZ_TC of
    Just co -> pure co
    Nothing -> panic "Data.Frag.Plugin initialize cound not find the KnownFragCard class's newtype"

  pure MkE{
      dynFlags0 = dflags
    ,
      piTrace = if tracing then tcPluginIO . putStrLn . showSDoc dflags else const (pure ())
    ,

      apartTC = apart_TC
    ,
      apartConsDC = apartCons_DC
    ,
      apartOneDC = apartOne_DC
    ,

      fragTC = frag_TC
    ,
      fragNilDC = fragNil_DC
    ,
      fragMinusTC = fragMinus_TC
    ,
      fragPlusTC = fragPlus_TC
    ,

      fragCardTC = fragCard_TC
    ,
      fragEQTC = fragEQ_TC
    ,
      fragLTTC = fragLT_TC
    ,
      fragNETC = fragNE_TC
    ,

      knownFragZTC = knownFragZ_TC
    ,
      setFragTC = setFrag_TC
    ,

      knownFragZCoax = knownFragZ_Coax
    ,
      unsafeConvertProxyIntId = ucpi
    ,
      unsafeProxyIntId = upi
    }
