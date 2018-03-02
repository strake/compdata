{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Desugar
-- Copyright   :  (c) 2011 Patrick Bahr, Tom Hvitved
-- License     :  BSD3
-- Maintainer  :  Tom Hvitved <hvitved@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This modules defines the 'Desugar' type class for desugaring of terms.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Desugar where

import           Data.Comp.Multi
import           Data.Comp.Multi.HTraversable


-- |The desugaring term homomorphism.
class (HFunctor f, HFunctor g) => Desugar f g where
    desugHom :: Hom f g
    desugHom = desugHom' . hfmap Hole
    desugHom' :: Alg f (Context g a)
    desugHom' x = appCxt (desugHom x)


-- We make the lifting to sums explicit in order to make the Desugar
-- class work with the default instance declaration further below.
instance {-# OVERLAPPING #-} (Desugar f h, Desugar g h) => Desugar (f :+: g) h where
    desugHom = caseH desugHom desugHom

-- |Desugar a term.
desugar :: Desugar f g => Term f :-> Term g
desugar = appHom desugHom

-- |Lift desugaring to annotated terms.
desugarA :: (HFunctor f', HFunctor g', DistAnn f p f', DistAnn g p g',
             Desugar f g) => Term f' :-> Term g'
desugarA = appHom (propAnn desugHom)

-- |Default desugaring instance.
instance {-# OVERLAPPABLE #-} (HFunctor f, HFunctor g, f :<: g) => Desugar f g where
    desugHom = simpCxt . inj


class (HTraversable f, HTraversable g, Monad m) => DesugarM m f g where
    desugHomM :: HomM m f g
    desugHomM = desugHomM' . hfmap Hole
    desugHomM' :: AlgM m f (Context g a)
    desugHomM' x = appCxt <$> desugHomM x

instance {-# OVERLAPPING #-} (DesugarM m f h, DesugarM m g h) => DesugarM m (f :+: g) h where
    desugHomM = caseH desugHomM desugHomM

desugarM :: DesugarM m f g => NatM m (Term f) (Term g)
desugarM = appHomM desugHomM

desugarMA :: (HTraversable f', HTraversable g', DistAnn f p f', DistAnn g p g', DesugarM m f g)
          => NatM m (Term f') (Term g')
desugarMA = appHomM (propAnnF desugHomM)

instance {-# OVERLAPPABLE #-} (HTraversable f, HTraversable g, f :<: g, Monad m) => DesugarM m f g where
    desugHomM = pure . simpCxt . inj
