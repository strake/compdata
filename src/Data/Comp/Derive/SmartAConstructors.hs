{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.SmartAConstructors
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive smart constructors with annotations.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.SmartAConstructors
    (
     smartAConstructors
    ) where

import Control.Monad
import Data.Comp.Annotation
import Data.Comp.Derive.Utils
import Data.Comp.Sum
import Data.Comp.Term
import Language.Haskell.TH hiding (Cxt)

{-| Derive smart constructors with products for a type constructor of any
  parametric kind taking at least one argument. The smart constructors are
  similar to the ordinary constructors, but an 'injectA' is automatically
  inserted. -}
smartAConstructors :: Name -> Q [Dec]
smartAConstructors fname = do
    Just (DataInfo _cxt _tname _targs constrs _deriving) <- abstractNewtypeQ $ reify fname
    let cons = map abstractConType constrs
    concat <$> mapM genSmartConstr cons
        where genSmartConstr   (name, args) = do
                let bname = nameBase name
                genSmartConstr'  (mkName $ "iA" ++ bname) name args
              genSmartConstr'  sname name args = do
                varNs <- newNames args "x"
                varPr <- newName "_p"
                let pats = map varP (varPr : varNs)
                    vars = map varE varNs
                    val = appE [|injectA $(varE varPr)|] $
                          appE [|inj|] $ foldl appE (conE name) vars
                    function = [funD sname [clause pats (normalB [|Term $val|]) []]]
                sequence function
