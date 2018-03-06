{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Decompose
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module implements the decomposition of terms into function
-- symbols and arguments resp. variables.
--
--------------------------------------------------------------------------------
module Data.Comp.Decompose (
  Decomp (..),
  DecompTerm,
  Decompose (..),
  decompose
  ) where

import Data.Comp.Term
import Data.Comp.Variables
import Data.Foldable

{-| This type represents decompositions of functorial values. -}

data Decomp f v a = Var v
                  | Fun (Const f) [a]

{-| This type represents decompositions of terms.  -}

type DecompTerm f v = Decomp f v (Term f)

{-| This class specifies the decomposability of a functorial value. -}

class (HasVars f v, Functor f, Foldable f) => Decompose f v where
    {-| This function decomposes a functorial value. -}

    decomp :: f a -> Decomp f v a
    decomp t = case isVar t of
                 Just v -> Var v
                 Nothing -> Fun (() <$ t) (toList t)

instance (HasVars f v, Functor f, Foldable f) => Decompose f v where


{-| This function decomposes a term. -}

decompose :: (Decompose f v) => Term f -> DecompTerm f v
decompose (Term t) = decomp t
