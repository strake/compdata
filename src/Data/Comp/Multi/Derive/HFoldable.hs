{-# LANGUAGE TemplateHaskell #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Multi.Derive.HFoldable
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @HFoldable@.
--
--------------------------------------------------------------------------------

module Data.Comp.Multi.Derive.HFoldable
    (
     HFoldable,
     makeHFoldable
    )where

import Control.Applicative
import Control.Monad
import Data.Comp.Derive.Utils
import Data.Comp.Multi.HFoldable
import Data.Comp.Multi.HFunctor
import Data.Foldable
import Data.Maybe
import Data.Monoid
import Language.Haskell.TH


iter 0 _ = id
iter n f = iter (n-1) f . appE f

iter' 0 _ = id
iter' m f = let f' = iter (m-1) [|fmap|] f
            in iter' (m-1) f . appE f'

iterSp n f g = run n
    where run 0 e = e
          run m e = let f' = iter (m-1) [|fmap|] (if n == m then g else f)
                    in run (m-1) (f' `appE` e)

{-| Derive an instance of 'HFoldable' for a type constructor of any higher-order
  kind taking at least two arguments. -}
makeHFoldable :: Name -> Q [Dec]
makeHFoldable fname = do
  Just (DataInfo _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let args' = init args
      fArg = VarT . tyVarBndrName $ last args'
      argNames = map (VarT . tyVarBndrName) (init args')
      complType = foldl AppT (ConT name) argNames
      classType = AppT (ConT ''HFoldable) complType
  constrs' <- mapM (mkPatAndVars . isFarg fArg <=< normalConExp) constrs
  foldDecl <- funD 'hfold (map foldClause constrs')
  foldMapDecl <- funD 'hfoldMap (map foldMapClause constrs')
  foldlDecl <- funD 'hfoldl (map foldlClause constrs')
  foldrDecl <- funD 'hfoldr (map foldrClause constrs')
  return [mkInstanceD [] classType [foldDecl,foldMapDecl,foldlDecl,foldrDecl]]
      where isFarg fArg (constr, args, gadtTy) = (constr, map (`containsType'` getBinaryFArg fArg gadtTy) args)
            filterVar [] _ = Nothing
            filterVar [d] x =Just (d, varE x)
            filterVar _ _ =  error "functor variable occurring twice in argument type"
            filterVars args varNs = catMaybes $ zipWith filterVar args varNs
            mkCPat constr args varNs = ConP constr $ zipWith mkPat args varNs
            mkPat [] _ = WildP
            mkPat _ x = VarP x
            mkPatAndVars (constr, args) =
                do varNs <- newNames (length args) "x"
                   return (mkCPat constr args varNs, filterVars args varNs)
            foldClause (pat,vars) =
                do let conApp (0,x) = [|unK $x|]
                       conApp (d,x) = iterSp d [|fold|] [| foldMap unK |] x
                   body <- if null vars
                           then [|mempty|]
                           else foldl1 (\ x y -> [|$x `mappend` $y|])
                                    $ map conApp vars
                   return $ Clause [pat] (NormalB body) []
            foldMapClause (pat,vars) =
                do fn <- newName "y"
                   let f = varE fn
                       f' 0 = f
                       f' n = iter (n-1) [|fmap|] [| foldMap $f |]
                       fp = if null vars then WildP else VarP fn
                   body <- case vars of
                             [] -> [|mempty|]
                             (_:_) -> foldl1 (\ x y -> [|$x `mappend` $y|]) $
                                      map (\ (d,z) -> iter' (max (d-1) 0) [|fold|] (f' d `appE` z)) vars
                   return $ Clause [fp, pat] (NormalB body) []
            foldlrClauses (pat,vars) =
                do fn <- newName "f"
                   en <- newName "e"
                   let f = varE fn
                       e = varE en
                       fp | null vars = WildP | otherwise = VarP fn
                       ep = VarP en
                       conAppL x (0,y) = [|$f $x $y|]
                       conAppL x (1,y) = [|foldl $f $x $y|]
                       conAppL x (d,y) = let hidEndo = iter (d-1) [|fmap|] [|Endo . flip (foldl $f)|] `appE` y
                                             endo = iter' (d-1) [|fold|] hidEndo
                                         in [| appEndo $endo $x|]
                       conAppR (0,x) y = [|$f $x $y|]
                       conAppR (1,x) y = [|foldr $f $y $x |]
                       conAppR (d,x) y = let hidEndo = iter (d-1) [|fmap|] [|Endo . flip (foldr $f)|] `appE` x
                                             endo = iter' (d-1) [|fold|] hidEndo
                                         in [| appEndo $endo $y|]
                       r body = Clause [fp, ep, pat] (NormalB body) []
                   liftA2 (,) (r <$> foldl conAppL e vars) (r <$> foldr conAppR e vars)
            foldlClause = fmap fst . foldlrClauses
            foldrClause = fmap snd . foldlrClauses
