{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Equality
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines equality for signatures, which lifts to equality for
-- terms and contexts.
--
--------------------------------------------------------------------------------
module Data.Comp.Equality
    (
     EqF(..),
     eqMod,
    ) where

import Control.Monad
import Data.Comp.Derive.Equality
import Data.Comp.Derive.Utils
import Data.Comp.Ops
import Data.Comp.Term
import Data.Foldable

-- instance (EqF f, Eq p) => EqF (f :*: p) where
--    eqF (v1 :*: p1) (v2 :*: p2) = p1 == p2 && v1 `eqF` v2

{-|
  From an 'EqF' functor an 'Eq' instance of the corresponding
  term type can be derived.
-}
instance (EqF f, Eq a) => Eq (Cxt h f a) where
    (==) = eqF

instance (EqF f) => EqF (Cxt h f) where
    eqF (Term e1) (Term e2) = e1 `eqF` e2
    eqF (Hole h1) (Hole h2) = h1 == h2
    eqF _ _ = False

{-|
  'EqF' is propagated through sums.
-}
instance (EqF f, EqF g) => EqF (f :+: g) where
    eqF (Inl x) (Inl y) = eqF x y
    eqF (Inr x) (Inr y) = eqF x y
    eqF _ _ = False

{-| This function implements equality of values of type @f a@ modulo
the equality of @a@ itself. If two functorial values are equal in this
sense, 'eqMod' returns a 'Just' value containing a list of pairs
consisting of corresponding components of the two functorial
values. -}
eqMod :: (EqF f, Functor f, Foldable f) => f a -> f b -> Maybe [(a,b)]
eqMod s t
    | unit s `eqF` unit' t = Just args
    | otherwise = Nothing
    where unit = fmap (const ())
          unit' = fmap (const ())
          args = toList s `zip` toList t

$(derive [makeEqF] $ [''Maybe, ''[]] ++ tupleTypes 2 10)
