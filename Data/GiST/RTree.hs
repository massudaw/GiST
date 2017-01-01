{- |
Module      :  RTree
Copyright   :  (c) Mihail Bogojeski
License     :  GPL

Maintainer  :  mihailbogojeski@gmail.com
Stability   :  experimental
Portability :  portable

A simple implementation of the R-Tree predicate. A containment predicate is a tuple of two points
representing a rectangle with the first tuple (minx,maxy) being the upper left corner of the rectangle
and the second (maxx,miny) being the lower right corner of the rectangle, while the equality predicate
is simply a 2D point (tuple of two integers).
-}


{-# LANGUAGE MultiParamTypeClasses
    , TypeFamilies
    , FlexibleInstances
    #-}

module Data.GiST.RTree (
    Predicate(..)
) where

import Data.GiST.GiST(Entry(..),entryPredicate,Predicates(..),Penalty)
import Data.GiST.BTree(between)
import Data.List(sort,sortBy,maximumBy)
import Data.Ord(comparing)
import qualified Data.Sequence as S


data Predicate a = Contains (a,a)               -- ^ containment predicate (rectangle)
                 | Equals a                     -- ^ equality predicate (2D point)
                 deriving (Eq,Ord,Show,Read)

-- Checks if the intervals of two R-Tree predicates overlap
overlaps :: (Ord a) => ((a,a),(a,a)) -> ((a,a),(a,a))  -> Bool
overlaps ((minx1,maxy1),(maxx1,miny1)) ((minx2,maxy2),(maxx2,miny2)) =  (minx1 <= maxx2)
                                                                && (minx2 <= maxx1)
                                                                && (miny1 <= maxy2)
                                                                && (miny2 <= maxy1)

-- | More documentation on the instance implementation in the source
instance Predicates (Predicate (Int,Int)) where

    type Penalty (Predicate (Int,Int)) = Int
    -- | Two containment predicates are consistent if the rectangles they represent overlap.
    -- A containment and equality predicate are consistent if the point represented by the latter
    -- is in the area described by former.
    -- Two equality predicates are consistent if they represent the same point
    consistent (Contains t1) (( Contains t2)) = overlaps t1 t2
    consistent (Equals (x,y)) (( Contains ((minx,maxy),(maxx,miny)))) = between x minx maxx && between y miny maxy
    consistent (Contains ((minx,maxy),(maxx,miny))) (( Equals (x,y))) = between x minx maxx && between y miny maxy
    consistent (Equals a1) (( Equals a2))           = a1 == a2

    -- | A union of predicates is a rectangle with the minimal x und maximal y coordinate of all predicates as the upper left corner
    -- and the maximal x and minimal y coordinate of all predicates as the lower right corner
    union ps = Contains ((minx,maxy),(maxx,miny))
                -- The minimum of all x interval minimums
        where   minx    = minimum $ fmap minxP ps
                -- The maximum of all y interval maximums
                maxy    = maximum $ fmap maxyP ps
                -- The maximum of all x interval maximums
                maxx    = maximum $ fmap maxxP ps
                -- The minimum of all y interval minimums
                miny    = minimum $ fmap minyP ps

    -- | Seperates the sorted list of entries into two halves using the linear split algorithm

    -- | The area increase of the second predicate after a union with the first
    penalty p1 p2  =  area (union (S.fromList [p1,p2])) - area p2


-- | The lower limit for the x coordinate of the predicate
minxP :: Predicate (a,a) -> a
minxP (Contains ((minx,_),(_,_))) = minx
minxP (Equals (x,_)) = x

-- | The upper limit for the y coordinate of the predicate
maxyP :: Predicate (a,a) -> a
maxyP (Contains ((_,maxy),(_,_))) = maxy
maxyP (Equals (_,y)) = y

-- | The upper limit for the x coordinate of the predicate
maxxP :: Predicate (a,a) -> a
maxxP (Contains ((_,_),(maxx,_))) = maxx
maxxP (Equals (x,_)) = x

-- | The lower limit for the y coordinate of the predicate
minyP :: Predicate (a,a) -> a
minyP (Contains ((_,_),(_,miny))) = miny
minyP (Equals (_,y)) = y

-- | Size of the area covered by the predicate
area :: Predicate (Int,Int) -> Int
area (Equals _) = 0
area (Contains ((minx,maxy),(maxx,miny))) = (maxx - minx) * (maxy - miny)



