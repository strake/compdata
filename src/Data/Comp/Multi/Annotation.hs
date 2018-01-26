{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Annotation
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines annotations on signatures. All definitions are
-- generalised versions of those in "Data.Comp.Annotation".
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Annotation
    (
     (:&:) (..),
     DistAnn (..),
     RemA (..),
     fmap,
     ann,
     fmap',
     stripA,
     propAnn,
     propAnnF,
     project'
    ) where

import Prelude hiding (fmap)
import Data.Comp.Multi.Algebra
import Data.Comp.Multi.HFunctor
import Data.Comp.Multi.Ops
import Data.Comp.Multi.Term
import qualified Data.Comp.Ops as O

-- | This function transforms a function with a domain constructed
-- from a functor to a function with a domain constructed with the
-- same functor but with an additional annotation.
fmap :: (RemA s s') => (s' a :-> t) -> s a :-> t
fmap f v = f (remA v)


-- | This function annotates each sub term of the given term with the
-- given value (of type a).

ann :: (DistAnn f p g, HFunctor f) => p -> CxtFun f g
ann c = appSigFun (injectA c)

-- | This function transforms a function with a domain constructed
-- from a functor to a function with a domain constructed with the
-- same functor but with an additional annotation.
fmap' :: (DistAnn s' p s, HFunctor s')
       => (s' a :-> Cxt h s' a) -> s a :-> Cxt h s a
fmap' f v = let (v' O.:&: p) = projectA v
             in ann p (f v')

{-| This function strips the annotations from a term over a
functor with annotations. -}

stripA :: (RemA g f, HFunctor g) => CxtFun g f
stripA = appSigFun remA


propAnn :: (DistAnn f p f', DistAnn g p g', HFunctor g)
               => Hom f g -> Hom f' g'
propAnn alg f' = ann p (alg f)
    where (f O.:&: p) = projectA f'

propAnnF :: (DistAnn f p f', DistAnn g p g', HFunctor g, Functor φ)
               => HomM φ f g -> HomM φ f' g'
propAnnF alg f' = ann p <$> alg f
    where (f O.:&: p) = projectA f'

-- | This function is similar to 'project' but applies to signatures
-- with an annotation which is then ignored.
project' :: (RemA f f', s :<: f') => Cxt h f a i -> Maybe (s (Cxt h f a) i)
project' (Term x) = proj $ remA x
project' _ = Nothing
