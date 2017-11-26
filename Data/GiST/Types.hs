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
    ,StandaloneDeriving
    ,FlexibleContexts
    ,ViewPatterns
    ,PatternSynonyms
    ,ScopedTypeVariables
    #-}

module Data.GiST.Types where

import Data.Foldable as F
import Data.Monoid
import Control.Monad (join)
import Data.Maybe
import Debug.Trace
import Control.DeepSeq
import Data.Tuple (swap)
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
data GiST p a  = Node !(Node p) !(Seq (GiST p a))      -- ^ internal node
               | Leaf !(Node p) !(Seq (LeafEntry p a))       -- ^ leaf node
               deriving (Functor,F.Foldable,T.Traversable,Generic)


deriving instance  (Eq (Node p ),Eq p ,Eq a )=>  Eq (GiST p a)
deriving instance  (Ord (Node p ),Ord p ,Ord a )=>  Ord (GiST p a)
deriving instance  (Show (Node p ),Show p ,Show a )=>  Show (GiST p a)


-- | A general entry type for the gist
data Entry p a = LeafEntry (LeafEntry p a)
               | NodeEntry (NodeEntry  p a)


unLeafEntry  (LeafEntry l) =  l
{-# INLINE unLeafEntry #-}
unNodeEntry  (NodeEntry n) =  n
{-# INLINE unNodeEntry #-}

nodePredicate :: GiST p a -> Node p
nodePredicate (Leaf p f) =  p
nodePredicate (Node p f) =  p
{-# INLINE nodePredicate #-}

-- | Returns the predicate of this entry
entryPredicate :: Entry p a -> Node p
entryPredicate (LeafEntry (_,e,_)) = e
entryPredicate (NodeEntry (Leaf e _ )) = e
entryPredicate (NodeEntry (Node e _ )) = e
{-# INLINE entryPredicate #-}

-- | A leaf entry has a predicate and data
type LeafEntry p a = (a, Node p,p)

-- | A node entry has a predicate and a subtree
type NodeEntry  p a = GiST p a


nodePred :: GiST p a  -> Node p
nodePred (Leaf p i) = p
nodePred (Node p i) = p
{-# INLINE nodePred #-}

-- | The predicate class that can be instanced by the user to create new types
-- of balanced search trees
class (Ord (Penalty p)) => Predicates p where
    type Penalty p
    data Node p
    type Query p
    -- | Checks if the given entry is consistent with a given predicate
    consistent  :: Either (Node p) p -> Either (Node p ) p -> Bool
    -- | Check if the given query is consistent with a given predicate
    match :: Query p -> Either (Node p) p -> Bool
    -- | Returns a predicate that is the union of all predicates of the given list of entries
    bound :: p -> Node p
    origin :: Node p
    merge :: Node p  -> Node p -> Node p

    -- | Calculates a numerical penalty for inserting the entry containing the first predicate
    -- into a subtree rooted at an entry containing the second predicate
    penalty  :: Node p -> Node p  -> Penalty p
    -- | Given a list of entries, returns two disjunct subsets that contain the entries in the list.
    -- Focus is on minimising the overlap between the splitted entries' predicates
    --pickSplitN :: Seq (Entry p b) -> (Node p ,Maybe b ,Seq (Node p,Maybe b,Seq (Entry p b)))
    pickSplit :: GiST p b -> (Node p ,Seq (GiST p b) ) -- -> (Seq (Seq (Entry  p b),Node p))
    pickSplit (Node pn l) =  (pn, S.fromList [uncurry Node (fmap unNodeEntry <$>  a),uncurry Node (fmap unNodeEntry <$> b)])
      where (a,b) = pickSplitG (fmap NodeEntry l)
    pickSplit (Leaf pn l) =  (pn, S.fromList [uncurry Leaf (fmap unLeafEntry <$>  a),uncurry Leaf (fmap unLeafEntry <$> b)])
      where (a,b) = pickSplitG (fmap LeafEntry l)



    chooseSubtree  :: Seq (NodeEntry p a) -> p  -> (NodeEntry p a,Int)
    chooseSubtree = chooseSubtreePenalty

union :: Predicates p => Seq (Node p) -> Node p
union l  = F.foldl' merge origin l
{-# INLINE union #-}

chooseSubtreePenalty :: Predicates p  =>Seq (NodeEntry  p a) -> p  -> (NodeEntry  p a,Int)
chooseSubtreePenalty subtrees e  = fromMaybe ({-traceShow ("choose(penalty,index,nodep)" , snd minP,snd $ fst minP ,e,nodePredicate (fst $ fst minP)) $-} fst  minP) se
  where   penalties = S.mapWithIndex (\k ne -> ((ne,k), penalty (bound e) (nodePred ne)) ) subtrees
          minP =minimumBy (comparing (\(~(_,p))-> p)) $ penalties
          minS = S.filter ((== snd minP).snd) penalties
          se = fmap (\i -> (S.index subtrees i, i)) $ S.findIndexL (not . L.null . searchKey e ) subtrees

searchKey  :: Predicates p  => p  -> GiST p a -> [(a, p)]
searchKey  p (Leaf _ es)     = fmap (\(i,j,k) -> (i,k)) $ F.toList $ S.filter (\(_,n,l)-> consistent (Right p)  (Left n ) && consistent (Right p) (Right l) ) es
searchKey  p (Node pn es) =
  concat $ fmap (\e -> if consistent (Right p) (Left $ nodePredicate e)
                 then searchKey p e  else []) es
searchKey _ (Node _ Empty) = []


leafValue (v,_,_) = v
leafNode (_,n,_) = n
leafPred (_,_,p) = p


greatestPenaltyLinear :: Predicates f  => Seq (Entry  f b) -> (Seq (Entry f b) , Entry f b, Entry f b)
greatestPenaltyLinear es = (items,e1,e2)
  where m = S.mapWithIndex (\ix1 e1 ->
             let li = deleteAt ix1 es
             in S.mapWithIndex (\ ix e ->
               let lii = deleteAt ix li
               in (lii,penalty (entryPredicate e1) (entryPredicate e),e1,e))li ) es
        (items,_,e1,e2)= maximumBy (comparing ((\(~(_,p,_,_)) ->p ))) $ maximumBy (comparing ((\(~(_,p,_,_)) ->p ))) <$>  m
{-# INLINE greatestPenaltyLinear #-}



-- | Implementation of the linear split algorithm taking the minimal fill factor into account
linearSplit :: (Predicates f  ) => (Node f,Seq (Entry f b)) -> (Node f,Seq (Entry f b)) ->
  Seq (Entry f b) -> Int -> ((Node f ,Seq (Entry f b)), (Node f ,Seq (Entry f b)))
linearSplit a1@(p1,es1) a2@(p2,es2) (e:<es) max
    |length es1 == max  = (a1,(union (p2 :< fmap entryPredicate (e:<es)),es2 <> (e:<es)))
    |length es2 == max  = ((union (p1:< fmap entryPredicate (e:<es)),es1 <> (e:<es)), a2 )
    |otherwise         = if penalty (entryPredicate e) p1 > penalty (entryPredicate e) p2
                            then linearSplit a1 u2 es max
                            else linearSplit u1 a2 es max
  where
    u1 = (merge (entryPredicate e) (p1),e:<es1)
    u2 = (merge (entryPredicate e) (p2),e:<es2)
linearSplit es1 es2 Empty _ = (es1,es2)
{-# INLINE linearSplit#-}



pickSplitG
  :: (Predicates f ) =>
    Seq (Entry f b) -> ((Node f ,Seq (Entry f b)), (Node f,Seq (Entry f b)))
pickSplitG es = linearSplit (entryPredicate e1,pure e1) ((entryPredicate e2),pure e2)  items len
        -- A tuple containing the two most disparate entries in the list their corresponding penalty penalty
        where (items, e1, e2) =  greatestPenaltyLinear es
              len = (S.length es + 1) `div` 2
{-# INLINE pickSplitG #-}

deleteAt ix s = h <> S.drop 1 t
  where (h,t) = S.splitAt ix  s

{-
instance (Show (Node p),Show p) => Show (GiST p a ) where
  show (Node  l ) = "N" ++ " [" ++ L.intercalate "," ( F.toList  $ fmap (\(g,p) ->   show p ++ " -> ("  ++ show g ++ ")") l) ++ "]"
  show (Leaf  l ) =  "L" ++" [" ++ L.intercalate "," (  F.toList  $fmap (\(g,p) ->   show p  ) l) ++ "]"
  show Null = "N"
-}

