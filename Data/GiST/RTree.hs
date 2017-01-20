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

import Data.GiST.GiST
import Debug.Trace
import Test.QuickCheck
import Data.List(sort,sortBy,maximumBy,nubBy)
import Data.Ord(comparing)
import qualified Data.Sequence as S


data Predicate a = Contains (a,a)               -- ^ containment predicate (rectangle)
                 | Equals a                     -- ^ equality predicate (2D point)
                 deriving (Eq,Ord,Show,Read)

-- Checks if the intervals of two R-Tree predicates overlap
overlaps :: (Ord a) => ((a,a),(a,a)) -> ((a,a),(a,a))  -> Bool
overlaps ((minx1,miny1),(maxx1,maxy1)) ((minx2,miny2),(maxx2,maxy2)) =  (minx1 <= maxx2)
                                                                && (minx2 <= maxx1)
                                                                && (miny1 <= maxy2)
                                                                && (miny2 <= maxy1)

-- | More documentation on the instance implementation in the source
instance Predicates (Int,Int) where

    type Node (Int,Int) = ((Int,Int),(Int,Int))
    type Penalty (Int,Int) = Int
    -- | Two containment predicates are consistent if the rectangles they represent overlap.
    -- A containment and equality predicate are consistent if the point represented by the latter
    -- is in the area described by former.
    -- Two equality predicates are consistent if they represent the same point

    -- consistent i j | traceShow  (i,j) False = undefined
    consistent (Left t1) ( Left t2) = overlaps t1 t2
    consistent (Right (x,y)) ( Left ((minx,miny),(maxx,maxy))) = between x minx maxx && between y miny maxy
    consistent (Left ((minx,miny),(maxx,maxy))) ( Right (x,y)) = between x minx maxx && between y miny maxy
    consistent (Right a1) ( Right a2)           = a1 == a2

    -- | A union of predicates is a rectangle with the minimal x und maximal y coordinate of all predicates as the upper left corner
    -- and the maximal x and minimal y coordinate of all predicates as the lower right corner
    bound i = (i,i)
    merge (Right (i,j) ) (Right (a,b)) = ((min i a ,min b j), (max i a,max b j))
    merge (Right (i,j) ) (Left ((a,b),(k,l))) = ((min i a, min j b),(max k i,max l j))
    merge  (Left ((a,b),(k,l))) (Right (i,j) ) = ((min i a, min j b),(max k i,max l j))
    merge  (Left ((a,b),(k,l))) (Left ((i,j),(c,d)))  = ((min i a, min j b),(max k c,max l d))
    -- | Seperates the sorted list of entries into two halves using the linear split algorithm

    -- | The area increase of the second predicate after a union with the first
    -- penalty p1 p2 | traceShow (p1,p2,merge p1 p2,area (Left $ merge p1 p2) - area p2 ) False = undefined
    penalty p1 p2  =  area (Left $ merge p1 p2) - area p2



-- | Size of the area covered by the predicate
area :: Either (Node (Int,Int)) (Int,Int) -> Int
area (Right _) = 1
area (Left ((minx,miny),(maxx,maxy))) = (max 1$  maxx - minx) * (max 1 $ maxy - miny)


between :: Ord a => a -> a -> a -> Bool
between a min max = (a >= min) && (a <= max)




addDeleteList :: [(Int,Int)] -> Bool
addDeleteList l = foldl (\g i -> delete i (3,6) g) (foldl (\g i  -> insert   i (3,6) g) empty (zip  [0..] l)) (reverse l) == (empty :: GiST (Int ,Int) Int)

addSearch :: [(Int,Int)] -> Bool
addSearch l = all (\(v,i) -> [v] == search i (foldl (\g  i -> insert  i (3,6) g) empty (zip  [(0::Int)..] l))) (nubBy (\i j -> snd i == snd j) $ reverse $ zip  [(0::Int) ..] l)



listitems ::  [(Int,Int)]
--listitems = [1,1]
--listitems = [0,1,7,7,2,2,7]
--listitems = [0,1,2,3,4,5,6,0]
listitems = [(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6)]
fullList,emptyList :: [GiST (Int,Int) Int]
fullList = scanl (\g i -> insert i (3,6) g) empty (zip [0..] listitems )
emptyList = scanl (\ g i -> delete i (3,6) g)(last fullList) (listitems) ++ scanl (\g i -> delete  i (3,6) g) (last fullList) (reverse listitems)
searchList = fmap (\(i,v) -> (i,v,   [v]== search i (last fullList ),   search i (last fullList )) ) (nubBy (\i j -> fst i == fst j) $ reverse $ zip listitems [(0::Int) ..])


