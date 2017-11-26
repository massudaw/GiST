{- |
Module      :  BTree
Copyright   :  (c) Mihail Bogojeski
License     :  GPL

Maintainer  :  mihailbogojeski@gmail.com
Stability   :  experimental
Portability :  portable

A simple implementation of the B+ tree predicate. A containment predicate is a tuple of two integers
representing an open interval, while the equality predicate is simply an interger value.
-}

{-# LANGUAGE MultiParamTypeClasses
  , TypeFamilies
  ,ViewPatterns
    ,PatternSynonyms
  , FlexibleInstances
    #-}



module Data.GiST.BTree (
    Predicate (..)
    ,between
) where

import Data.GiST.GiST
import Data.GiST.Types
import Data.List(sort,sortBy)
import qualified Data.List as L
import Data.Monoid
import Data.Semigroup
import Test.QuickCheck
import Data.Foldable
import Debug.Trace
import Data.Ord

import qualified Data.Sequence as S


data Predicate a = Contains (a,a)                   -- ^ containment predicate (interval)
                 | Equals a                         -- ^ equality predicate (integer value)
                 deriving (Eq, Ord, Show, Read)



instance Monoid (Node Int) where
  mempty = Range (maxBound,minBound)
  mappend (Range (a,b))  (Range (c,d)) = Range (min a c, max b d)

-- | More documentation on the instance implementation in the source
instance Predicates Int where
    type Penalty Int = Int
    type Query Int = Predicate Int
    data Node Int = Range (Int,Int) deriving (Eq,Ord,Show)

    -- | Two containment predicates are consistent if the intervals they represent overlap
    -- A containment and equality predicate are consistent if the interval represented by the former contains the value of the latter
    -- Two equality predicates are consistent if they represent the same value
    -- consistent  i j | traceShow (i,j) False = undefined
    consistent (Left (Range (min1,max1))) (Left (Range (min2,max2)) ) = (min1 <= max2) && (max1 >= min2)
    consistent (Right  a) (Left (Range (min,max))) = between a min max
    consistent (Left (Range (min,max))) (Right  a)= between a min max
    consistent (Right a1) (Right a2)  = a1 == a2
    match (Equals i)  j = consistent (Right i) j
    match (Contains i)  j = consistent (Left (Range i)) j

    -- | A union of predicates is an interval spanning from the minimal
    -- to the maximal value of all the predicats
    bound i  =  Range (i,i)

    origin  = mempty
    merge = mappend

    pickSplit (Node pn es) = (pn , S.fromList [Node pl l , Node pj j ])
        where
          pl = union (nodePredicate <$> l)
          pj = union (nodePredicate <$> j)
          (l,j)  = S.splitAt ((length es + 1) `div` 2) sorted
          sorted  = S.sortBy (comparing nodePredicate) es
    pickSplit (Leaf pn es )= (pn, S.fromList [Leaf pl l , Leaf pj j])
      where
        pl = union (leafNode <$> l)
        pj = union (leafNode <$> j)
        (l,j)  = S.splitAt ((length es + 1) `div` 2) sorted
        sorted  = S.sortBy (comparing leafPred) es

    -- | The distance between the intervals (or values) of the predicates
    penalty p1 p2 = max 0 ((minP p2)-(minP p1)) + max 0 ((maxP p1)-(maxP p2))

-- The lower limit of the predicate
minP :: (Node Int) -> Int
minP (Range (min,_)) = min

-- The upper limit of the predicate
maxP :: (Node Int) -> Int
maxP (Range (_,max)) = max


-- | Tests if a value is between two others
between :: Ord a => a -> a -> a -> Bool
between a min max = (a >= min) && (a <= max)


addDeleteList :: [Int] -> Bool
addDeleteList l = foldl (\g i -> delete i (3,6) g) (foldl (\g i  -> insert   i (3,6) g) empty (zip  [0..] l)) (reverse l) == (empty :: GiST Int Int)

addSearch :: [Int] -> Bool
addSearch l = all (\(v,i) -> [v] == search i (foldl (\g  i -> insert  i (3,6) g) empty (zip  [(0::Int)..] l))) (L.nubBy (\i j -> snd i == snd j) $ reverse $ zip  [(0::Int) ..] l)



listitems ::  [Int]
--listitems = [1,1]
--listitems = [0,1,7,7,2,2,7]
--listitems = [0,1,2,3,4,5,6,0]
listitems = [3,5,0,4,1,2,6,0]
fullList,emptyList :: [GiST Int Int]
fullList = scanl (\g i -> insert i (3,6) g) empty (zip [0..] listitems )
emptyList = scanl (\ g i -> delete i (3,6) g)(last fullList) (listitems) ++ scanl (\g i -> delete  i (3,6) g) (last fullList) (reverse listitems)
searchList = fmap (\(i,v) -> (i,v,   [v]== search i (last fullList ),   search i (last fullList )) ) (L.nubBy (\i j -> fst i == fst j) $ reverse $ zip listitems [(0::Int) ..])


