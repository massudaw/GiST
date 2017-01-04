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
    ,Prefix(..)
    ,between
) where

import Data.GiST.GiST(Entry(..),entryPredicate,Predicates(..),Penalty,union)
import Data.List(sort,sortBy)
import qualified Data.List as L
import Data.Monoid
import Data.Semigroup
import Data.Foldable
import Data.Ord

import qualified Data.Sequence as S


data Predicate a = Contains (a,a)                   -- ^ containment predicate (interval)
                 | Equals a                         -- ^ equality predicate (integer value)
                 deriving (Eq, Ord, Show, Read)



-- | More documentation on the instance implementation in the source
instance Predicates Int where
    type Penalty Int = Int
    type Query Int = Predicate Int
    type Node Int = (Int,Int)

    -- | Two containment predicates are consistent if the intervals they represent overlap
    -- A containment and equality predicate are consistent if the interval represented by the former contains the value of the latter
    -- Two equality predicates are consistent if they represent the same value
    consistent (Left (min1,max1)) (Left (min2,max2) ) = (min1 <= max2) && (max1 >= min2)
    consistent (Right  a) (Left (min,max)) = between a min max
    consistent  (Left (min,max)) (Right  a)= between a min max
    consistent (Right a1) (Right a2)  = a1 == a2
    match (Equals i)  j = consistent (Right i) j
    match (Contains i)  j = consistent (Left i) j

    -- | A union of predicates is an interval spanning from the minimal
    -- to the maximal value of all the predicats
    bound (Right i ) = (i,i)
    bound (Left i ) = i
    merge (Right i ) (Right j) = (min i j ,max i j)
    merge (Left (a,b) ) (Left (c,d)) = (min a c, max b d)
    merge (Right a ) (Left (c,d)) = (min a c, max a d)
    merge  (Left (c,d)) (Right a )= (min a c, max a d)

    pickSplit es = ((union (entryPredicate <$> l) ,l),(union (entryPredicate <$> l),j))
        where
          (l,j)  = S.splitAt ((length es + 1) `div` 2) sorted
          sorted  = S.sortBy (comparing entryPredicate) es

    -- | The distance between the intervals (or values) of the predicates
    penalty p1 p2 = max 0 ((minP p2)-(minP p1)) + max 0 ((maxP p1)-(maxP p2))

-- The lower limit of the predicate
minP :: Either (a,a) a -> a
minP (Left (min,_)) = min
minP (Right a) = a

-- The upper limit of the predicate
maxP :: Either (a,a) a -> a
maxP (Left (_,max)) = max
maxP (Right a) = a

pattern Empty   <- (S.viewl -> S.EmptyL)  where Empty = S.empty
pattern x :< xs <- (S.viewl -> x S.:< xs) where (:<)  = (S.<|)
pattern xs :> x <- (S.viewr -> xs S.:> x) where (:>)  = (S.|>)

-- | Tests if a value is between two others
between :: Ord a => a -> a -> a -> Bool
between a min max = (a >= min) && (a <= max)
