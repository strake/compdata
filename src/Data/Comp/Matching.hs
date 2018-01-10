{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Matching
-- Copyright   :  (c) 2010-2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- This module implements matching of contexts or terms with variables againts terms
--
--------------------------------------------------------------------------------

module Data.Comp.Matching
    (
     matchCxt,
     matchTerm,
     module Data.Comp.Variables
    ) where

import Data.Comp.Equality
import Data.Comp.Term
import Data.Comp.Variables
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable

import Prelude hiding (all, mapM, mapM_)

{-| This is an auxiliary function for implementing 'matchCxt'. It behaves
similarly as 'match' but is oblivious to non-linearity. Therefore, the
substitution that is returned maps holes to non-empty lists of terms
(resp. contexts in general). This substitution is only a matching
substitution if all elements in each list of the substitution's range
are equal. -}

matchCxt' :: (Ord v, EqF f, Functor f, Foldable f)
       => Context f v -> Cxt h f a -> Maybe (Map v [Cxt h f a])
matchCxt' (Hole v) t = Just $  Map.singleton v [t]
matchCxt' (Term s) (Term t) =
  Map.unionsWith (++) <$> (eqMod s t >>= mapM (uncurry matchCxt'))
matchCxt' Term {} Hole {} = Nothing


{-| This function takes a context @c@ as the first argument and tries
to match it against the term @t@ (or in general a context with holes
in @a@). The context @c@ matches the term @t@ if there is a
/matching substitution/ @s@ that maps holes to terms (resp. contexts in general)
such that if the holes in the context @c@ are replaced according to
the substitution @s@, the term @t@ is obtained. Note that the context
@c@ might be non-linear, i.e. has multiple holes that are
equal. According to the above definition this means that holes with
equal holes have to be instantiated by equal terms! -}

matchCxt :: (Ord v,EqF f, Eq (Cxt h f a), Functor f, Foldable f)
         => Context f v -> Cxt h f a -> Maybe (CxtSubst h a f v)
matchCxt c1 c2 = do
  res <- matchCxt' c1 c2
  let insts = Map.elems res
  mapM_ checkEq insts
  return $ Map.map head res
    where checkEq [] = Nothing
          checkEq (c : cs)
              | all (== c) cs = Just ()
              | otherwise = Nothing

{-| This function is similar to 'matchCxt' but instead of a context it
matches a term with variables against a context.  -}

matchTerm :: (Ord v, EqF f, Eq (Cxt h f a) , Traversable f, HasVars f v)
          => Term f -> Cxt h f a -> Maybe (CxtSubst h a f v)
matchTerm t = matchCxt (varsToHoles t)

