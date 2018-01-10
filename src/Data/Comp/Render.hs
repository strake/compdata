{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Data.Comp.Render where

import Data.Comp hiding (fmap)
import Data.Comp.Derive
import Data.Comp.Show ()
import Data.Foldable (toList)
import Data.Tree (Tree (..))
import Data.Tree.View

-- | The 'stringTree' algebra of a functor. The default instance creates a tree
-- with the same structure as the term.
class (Functor f, Foldable f, ShowConstr f) => Render f where
    stringTreeAlg :: Alg f (Tree String)
    stringTreeAlg f = Node (showConstr f) $ toList f

-- | Convert a term to a 'Tree'
stringTree :: Render f => Term f -> Tree String
stringTree = cata stringTreeAlg

-- | Show a term using ASCII art
showTerm :: Render f => Term f -> String
showTerm = showTree . stringTree

-- | Print a term using ASCII art
drawTerm :: Render f => Term f -> IO ()
drawTerm = putStrLn . showTerm

-- | Write a term to an HTML file with foldable nodes
writeHtmlTerm :: Render f => FilePath -> Term f -> IO ()
writeHtmlTerm file
    = writeHtmlTree Nothing file
    . fmap (\n -> NodeInfo InitiallyExpanded n "") . stringTree

$(derive [liftSum] [''Render])
