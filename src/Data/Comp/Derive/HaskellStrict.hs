{-# LANGUAGE CPP              #-}
{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TypeOperators    #-}
--------------------------------------------------------------------------------
-- |
-- Module      :  Data.Comp.Derive.HaskellStrict
-- Copyright   :  (c) 2011 Patrick Bahr
-- License     :  BSD3
-- Maintainer  :  Patrick Bahr <paba@diku.dk>
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Automatically derive instances of @HaskellStrict@.
--
--------------------------------------------------------------------------------

module Data.Comp.Derive.HaskellStrict
  ( makeHaskellStrict
  , haskellStrict
  , haskellStrict'
  )
where

import           Data.Comp.Derive.Utils
import           Data.Comp.Sum
import           Data.Comp.Thunk
import           Data.Maybe
import           Language.Haskell.TH


class HaskellStrict f where
    thunkSequence :: (Monad m) => f (TermT m g) -> m (f (TermT m g))
    thunkSequenceInject :: (Monad m, f :<: m :+: g) => f (TermT m g) -> TermT m g
    thunkSequenceInject t = thunk $ inject <$> thunkSequence t
    thunkSequenceInject' :: (Monad m, f :<: m :+: g) => f (TermT m g) -> TermT m g
    thunkSequenceInject' = thunkSequenceInject

haskellStrict :: (Monad m, HaskellStrict f, f :<: m :+: g) => f (TermT m g) -> TermT m g
haskellStrict = thunkSequenceInject

haskellStrict' :: (Monad m, HaskellStrict f, f :<: m :+: g) => f (TermT m g) -> TermT m g
haskellStrict' = thunkSequenceInject'

deepThunk d = iter d [|thunkSequence|]
    where iter 0 _ = [|whnf'|]
          iter 1 e = e
          iter n e = iter (n-1) ([|mapM|] `appE` e)

{-| Derive an instance of 'HaskellStrict' for a type constructor of any
  first-order kind taking at least one argument. -}
makeHaskellStrict :: Name -> Q [Dec]
makeHaskellStrict fname = do
  Just (DataInfo _cxt name args constrs _deriving) <- abstractNewtypeQ $ reify fname
  let fArg = VarT . tyVarBndrName $ last args
      argNames = map (VarT . tyVarBndrName) (init args)
      complType = foldl AppT (ConT name) argNames
      classType = AppT (ConT ''HaskellStrict) complType
  constrs_ <- mapM (fmap (isFarg fArg) . normalConStrExp) constrs
  if foldr (\ y x -> x && all null (snd y)) True constrs_
   then do
     sequenceDecl <- valD (varP 'thunkSequence) (normalB [|return|]) []
     injectDecl <- valD (varP 'thunkSequenceInject) (normalB [|inject|]) []
     injectDecl' <- valD (varP 'thunkSequenceInject') (normalB [|inject|]) []
     return [mkInstanceD [] classType [sequenceDecl, injectDecl, injectDecl']]
   else do
     (sc',matchPat,ic') <- unzip3 <$> mapM mkClauses constrs_
     xn <- newName "x"
     doThunk <- [|thunk|]
     let sequenceDecl = FunD 'thunkSequence sc'
         injectDecl = FunD 'thunkSequenceInject [Clause [VarP xn] (NormalB (doThunk `AppE` CaseE (VarE xn) matchPat)) []]
         injectDecl' = FunD 'thunkSequenceInject' ic'
     return [mkInstanceD [] classType [sequenceDecl, injectDecl, injectDecl']]
      where isFarg fArg (constr, args, gadtTy) = (constr, map (containsStr (getUnaryFArg fArg gadtTy)) args)

#if __GLASGOW_HASKELL__ < 800
            containsStr fArg (IsStrict,ty) = ty `containsType'` fArg
            containsStr fArg (Unpacked,ty) = ty `containsType'` fArg
#else
            containsStr fArg (Bang _ SourceStrict,ty) = ty `containsType'` fArg
            containsStr fArg (Bang SourceUnpack _,ty) = ty `containsType'` fArg
#endif
            containsStr _ _ = []

            filterVar _ nonFarg [] x  = nonFarg x
            filterVar farg _ [depth] x = farg depth x
            filterVar _ _ _ _ = error "functor variable occurring twice in argument type"
            filterVars args varNs farg nonFarg = zipWith (filterVar farg nonFarg) args varNs
            mkCPat constr varNs = ConP constr $ map mkPat varNs
            mkPat = VarP
            mkClauses (constr, args) =
                do varNs <- newNames (length args) "x"
                   let pat = mkCPat constr varNs
                       fvars = catMaybes $ filterVars args varNs (curry Just) (const Nothing)
                       allVars = map varE varNs
                       conAp = foldl appE (conE constr) allVars
                       conBind (d, x) y = [| $(deepThunk d `appE` varE x)  >>= $(lamE [varP x] y)|]
                   bodySC' <- foldr conBind [|return $conAp|] fvars
                   let sc' = Clause [pat] (NormalB bodySC') []
                   bodyMatch <- case fvars of
                             [] -> [|return (inject $conAp)|]
                             _ -> foldr conBind [|return (inject $conAp)|] fvars
                   let matchPat = Match pat (NormalB bodyMatch) []
                   bodyIC' <- case fvars of
                             [] -> [|inject $conAp|]
                             _ -> [| thunk |] `appE` foldr conBind [|return (inject $conAp)|] fvars
                   let ic' = Clause [pat] (NormalB bodyIC') []
                   return (sc', matchPat, ic')
