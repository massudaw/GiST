{- |
Module      :  Types
Copyright   :  (c) Mihail Bogojeski, Alexander Svozil
License     :  GPL

Maintainer  :  mihailbogojeski@gmail.com
Stability   :  experimental
Portability :  portable

Defines the basic types used for this GiST implementation and a couple of operations on these types.
Also introduces the Predicates class which the user of this package can instance to create predicates
which define the data stored in the tree and the tree's behavior during insert, delete, and search operations
-}


{-# LANGUAGE MultiParamTypeClasses
    ,FlexibleInstances
    ,TypeFamilies
    ,DeriveFunctor
    ,DeriveFoldable
    ,DeriveTraversable
    ,DeriveGeneric
    ,FlexibleContexts
    ,ViewPatterns
    ,PatternSynonyms
    ,ScopedTypeVariables
    #-}

module Data.GiST.Types where

import Data.Foldable as F
import Data.Monoid
import Control.Monad (join)
import Control.DeepSeq
import GHC.Generics
import Data.Traversable as T
import Data.Ord
import Data.Maybe (fromJust,isJust)
import qualified Data.Sequence as S
import Data.Sequence ( Seq)
import qualified Data.List as L


import qualified Data.Sequence as Seq

pattern Empty   <- (S.viewl -> S.EmptyL)  where Empty = S.empty
pattern x :< xs <- (S.viewl -> x S.:< xs) where (:<)  = (S.<|)
pattern xs :> x <- (S.viewr -> xs S.:> x) where (:>)  = (S.|>)


-- | The data structure used for building the GiST
data GiST p a  = Leaf !(Seq (LeafEntry p a))       -- ^ leaf node
               | Node !(Seq (NodeEntry GiST p a))      -- ^ internal node
               | Null                       -- ^ a null GiST
               deriving (Functor,F.Foldable,T.Traversable,Generic)




-- | A general entry type for the gist
data Entry f p a = LeafEntry !(LeafEntry p a)
                 | NodeEntry !(NodeEntry f p a)


unLeafEntry  (LeafEntry l) =  l
{-# INLINE unLeafEntry #-}
unNodeEntry  (NodeEntry n) =  n
{-# INLINE unNodeEntry #-}

-- | Returns the predicate of this entry
entryPredicate :: Entry f p a -> Either (Node p) p
entryPredicate (LeafEntry e) = Right $ snd e
entryPredicate (NodeEntry e) = Left $ snd e
{-# INLINE entryPredicate #-}

-- | A leaf entry has a predicate and data
type LeafEntry p a = (a, p )

-- | A node entry has a predicate and a subtree
type NodeEntry f p a = (f p a, Node p )


-- | The predicate class that can be instanced by the user to create new types
-- of balanced search trees
class (Ord (Penalty p)) => Predicates p where
    type Penalty p
    type Node p
    type Query p
    data Prefix p
    -- | Checks if the given entry is consistent with a given predicate
    consistent  :: Either (Node p) p -> Either (Node p ) p -> Bool
    -- | Check if the given query is consistent with a given predicate
    match :: Query p -> Either (Node p) p -> Bool
    -- | Returns a predicate that is the union of all predicates of the given list of entries
    bound :: Either (Node p) p -> Node p
    merge :: Either (Node p) p -> Either (Node p) p -> Node p

    -- | Calculates a numerical penalty for inserting the entry containing the first predicate
    -- into a subtree rooted at an entry containing the second predicate
    penalty  :: Either (Node p) p -> Either (Node p ) p  -> Penalty p
    -- | Given a list of entries, returns two disjunct subsets that contain the entries in the list.
    -- Focus is on minimising the overlap between the splitted entries' predicates
    pickSplit :: Seq (Entry f p b) -> ((Node p,Seq (Entry f p b)), (Node p,Seq (Entry f p b)))
    pickSplit = pickSplitG
    pickSplitN :: Seq (Entry f p b) -> Seq (Node p,Seq (Entry f p b))
    chooseTree :: LeafEntry  p  b -> Seq (Entry f p b) -> (Entry f p b,Seq (Entry f p b))

union :: Predicates p => Seq (Either (Node p) p) -> Node p
union l  = case S.viewl l of
    i S.:< ps -> F.foldl' (\i l-> merge (Left i) l ) (bound i) ps
{-# INLINE union #-}

greatestPenaltyLinear :: (Predicates f  ) => Seq (Entry g f b) -> (Seq (Entry g f b) , Entry g f b, Entry g f b)
greatestPenaltyLinear es = (items,e1,e2)
  where m = S.mapWithIndex (\ix1 e1 ->
             let li = deleteAt ix1 es
             in S.mapWithIndex (\ ix e ->
               let lii = deleteAt ix li
               in (lii,penalty (entryPredicate e1) (entryPredicate e),e1,e))li ) es
        (items,_,e1,e2)= maximumBy (comparing ((\(~(_,p,_,_)) ->p ))) $ maximumBy (comparing ((\(~(_,p,_,_)) ->p ))) <$>  m
{-# INLINE greatestPenaltyLinear #-}




-- | Implementation of the linear split algorithm taking the minimal fill factor into account
linearSplit :: (Predicates f  ) => (Node f,Seq (Entry g f b)) -> (Node f,Seq (Entry g f b)) ->
  Seq (Entry g f b) -> Int -> ((Node f ,Seq (Entry g f b)), (Node f ,Seq (Entry g f b)))
linearSplit a1@(p1,es1) a2@(p2,es2) (e:<es) max
    |length es1 == max  = (a1,(union (Left p2 :< fmap entryPredicate (e:<es)),es2 <> (e:<es)))
    |length es2 == max  = ((union (Left p1:< fmap entryPredicate (e:<es)),es1 <> (e:<es)), a2 )
    |otherwise         = if penalty (entryPredicate e) (Left $ p1) >
                            penalty (entryPredicate e) (Left $ p2)
                            then linearSplit a1 u2 es max
                            else linearSplit u1 a2 es max
  where
    u1 = (merge (entryPredicate e ) (Left p1),e:<es1)
    u2 = (merge (entryPredicate e ) (Left p2),e:<es2)
linearSplit es1 es2 Empty _ = (es1,es2)
{-# INLINE linearSplit#-}


pickSplitG
  :: (Predicates f ) =>
    Seq (Entry g f b) -> ((Node f ,Seq (Entry g f b)), (Node f,Seq (Entry g f b)))
pickSplitG es = linearSplit (bound (entryPredicate e1),pure e1) (bound (entryPredicate e2),pure e2)  items len
        -- A tuple containing the two most disparate entries in the list their corresponding penalty penalty
        where (items, e1, e2) =  greatestPenaltyLinear es
              len = (S.length es + 1) `div` 2
{-# INLINE pickSplitG #-}

deleteAt ix s = h <> S.drop 1 t
  where (h,t) = S.splitAt ix  s

instance (Show (Node p),Show p) => Show (GiST p a ) where
  show (Node  l ) = "N" ++ " [" ++ L.intercalate "," ( F.toList  $ fmap (\(g,p) ->   show p ++ " -> ("  ++ show g ++ ")") l) ++ "]"
  show (Leaf  l ) =  "L" ++" [" ++ L.intercalate "," (  F.toList  $fmap (\(g,p) ->   show p  ) l) ++ "]"
  show Null = "N"


