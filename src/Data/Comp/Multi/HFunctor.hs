{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE IncoherentInstances       #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.HFunctor
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines higher-order functors (Johann, Ghani, POPL
-- '08), i.e. endofunctors on the category of endofunctors.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.HFunctor
    (
     HFunctor (..),
     (:->),
     (:=>),
     NatM,
     I (..),
     K (..),
     A (..),
     E (..),
     runE,
     (:.:)(..)
     ) where

import Data.Traversable
import Data.Foldable
import Data.Functor.Classes
import Data.Functor.Compose
import Data.Semigroup

-- | The identity Functor.
newtype I a = I {unI :: a} deriving (Functor, Foldable, Traversable)


-- | The parametrised constant functor.
newtype K a i = K {unK :: a} deriving (Functor, Foldable, Traversable)

data E f = forall i. E {unE :: f i}

runE :: (f :=> b) -> E f -> b
runE f (E x) = f x

newtype A f = A {unA :: forall i. f i}

instance Eq a => Eq (K a i) where
    K x == K y = x == y
    K x /= K y = x /= y

instance Ord a => Ord (K a i) where
    K x < K y = x < y
    K x > K y = x > y
    K x <= K y = x <= y
    K x >= K y = x >= y
    min (K x) (K y) = K $ min x y
    max (K x) (K y) = K $ max x y
    compare (K x) (K y) = compare x y


infixr 0 :-> -- same precedence as function space operator ->
infixr 0 :=> -- same precedence as function space operator ->

-- | This type represents natural transformations.
type f :-> g = forall i . f i -> g i

-- | This type represents co-cones from @f@ to @a@. @f :=> a@ is
-- isomorphic to f :-> K a
type f :=> a = forall i . f i -> a


type NatM m f g = forall i. f i -> m (g i)

-- | This class represents higher-order functors (Johann, Ghani, POPL
-- '08) which are endofunctors on the category of endofunctors.
class HFunctor h where
    -- A higher-order functor @f@ maps every functor @g@ to a
    -- functor @f g@.
    --
    -- @ffmap :: (Functor g) => (a -> b) -> f g a -> f g b@
    --
    -- We omit this, as it does not work for GADTs (see Johand and
    -- Ghani 2008).

    -- | A higher-order functor @f@ also maps a natural transformation
    -- @g :-> h@ to a natural transformation @f g :-> f h@
    hfmap :: (f :-> g) -> h f :-> h g

instance (Functor f) => HFunctor (Compose f) where hfmap f (Compose xs) = Compose (fmap f xs)

infixl 5 :.:

-- | This data type denotes the composition of two functor families.
newtype (:.:) f g e t = Comp (f (g e) t)
  deriving (Eq, Ord, Read, Show, Semigroup, Monoid, Bounded,
            Functor, Foldable, Traversable, Applicative, Monad, Eq1, Ord1, Read1, Show1)

instance (HFunctor f, HFunctor g) => HFunctor (f :.: g) where
    hfmap f (Comp x) = Comp (hfmap (hfmap f) x)
