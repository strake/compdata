module Data.Comp.Equality_Test where


import Control.Arrow ((***))

import Data.Comp
import Data.Comp.Equality
import Data.Comp.Arbitrary
import Data.Comp.Show

import Test.Framework
import Test.Framework.Providers.QuickCheck2
import Test.QuickCheck
import Test.Utils





--------------------------------------------------------------------------------
-- Test Suits
--------------------------------------------------------------------------------

main = defaultMain [tests]

tests = testGroup "Equality" [
         testProperty "prop_eqMod_fmap" prop_eqMod_fmap
        ]


--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_eqMod_fmap cxt f = case eqMod cxt (f <$> cxt) of
                   Nothing -> False
                   Just list -> all (uncurry (==)) $ map (f *** id) list
    where _ = (cxt :: Context SigP Int, f :: Int -> Int)
