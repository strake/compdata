{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Generic
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module defines type generic functions and recursive schemes
-- along the lines of the Uniplate library.
--
--------------------------------------------------------------------------------

module Data.Comp.Generic where

import Control.Monad hiding (mapM)
import Data.Comp.Algebra
import Data.Comp.Sum
import Data.Comp.Term
import Data.Foldable
import Data.Maybe
import Data.Traversable
import GHC.Exts (build)
import Prelude hiding (foldl, mapM)


-- | This function returns the subterm of a given term at the position
-- specified by the given path or @Nothing@ if the input term has no
-- such subterm

getSubterm :: (Functor g, Foldable g) => [Int] -> Term g -> Maybe (Term g)
getSubterm path t = cata alg t path where
    alg :: (Functor g, Foldable g) => Alg g ([Int] -> Maybe (Cxt h g a))
    alg t [] = Just $ Term $ fmap (fromJust . ($[])) t
    alg t (i:is) = case drop i (toList t) of
                     [] -> Nothing
                     x : _ -> x is

-- | This function returns a list of all subterms of the given
-- term. This function is similar to Uniplate's @universe@ function.
subterms :: forall f . Foldable f => Term f -> [Term f]
subterms t = build (f t)
    where f :: Term f -> (Term f -> b -> b) -> b -> b
          f t cons nil = t `cons` foldl (\u s -> f s cons u) nil (unTerm t)
-- universe t = t : foldl (\u s -> u ++ universe s) [] (unTerm t)


-- | This function returns a list of all subterms of the given term
-- that are constructed from a particular functor.
subterms' :: forall f g . (Foldable f, g :<: f) => Term f -> [g (Term f)]
subterms' (Term t) = build (f t)
    where f :: f (Term f) -> (g (Term f) -> b -> b) -> b -> b
          f t cons nil = let rest = foldl (\u (Term s) -> f s cons u) nil t
                         in case proj t of
                              Just t' -> t'`cons` rest
                              Nothing -> rest

-- | This function transforms every subterm according to the given
-- function in a bottom-up manner. This function is similar to
-- Uniplate's @transform@ function.
transform :: (Functor f) => (Term f -> Term f) -> Term f -> Term f
transform f = run
    where run = f . Term . fmap run . unTerm
-- transform f  = f . Term . fmap (transform f) . unTerm

transform' :: (Functor f) => (Term f -> Maybe (Term f)) -> Term f -> Term f
transform' f = transform f' where
    f' t = fromMaybe t (f t)


-- | Monadic version of 'transform'.
transformM :: (Traversable f, Monad m) =>
             (Term f -> m (Term f)) -> Term f -> m (Term f)
transformM  f = run
    where run t = f =<< fmap Term (mapM run $ unTerm t)

query :: Foldable f => (Term f -> r) -> (r -> r -> r) -> Term f -> r
query q c = run
    where run i@(Term t) = foldl (\s x -> s `c` run x) (q i) t
-- query q c i@(Term t) = foldl (\s x -> s `c` query q c x) (q i) t

gsize :: Foldable f => Term f -> Int
gsize = query (const 1) (+)

-- | This function computes the generic size of the given term,
-- i.e. the its number of subterm occurrences.
size :: Foldable f => Cxt h f a -> Int
size (Hole {}) = 0
size (Term t) = foldl (\s x -> s + size x) 1 t

-- | This function computes the generic height of the given term.
height :: Foldable f => Cxt h f a -> Int
height (Hole {}) = 0
height (Term t) = 1 + foldl (\s x -> s `max` height x) 0 t
