{-# LANGUAGE StandaloneDeriving,TupleSections,PatternSynonyms,ViewPatterns,FlexibleInstances,DeriveTraversable , DeriveFoldable,DeriveFunctor,DeriveGeneric,TypeFamilies ,FlexibleContexts,ScopedTypeVariables #-}
module Data.GiST.QuadTree where

import Data.GiST.SPGiST
import Data.Tuple
import Data.Either (isRight,isLeft)
import Data.Monoid
import Data.Ord
import Control.Applicative hiding (empty)
import Data.List (intercalate,sort)
import qualified Data.List as L
import Data.Maybe
import Debug.Trace
import Data.Sequence (Seq)
import qualified Data.Sequence as S
import qualified Data.Foldable as F
import qualified Data.Traversable as T
import Test.QuickCheck
import GHC.Generics (Generic)
import qualified Data.Sequence as Seq


---------------------
-- QuadTree Predicate  --
---------------------

instance (Show a,Fractional a ,Ord a ,Num a) => Predicates (a,a) where
  data Node (a,a) = Center (a,a) deriving(Eq,Ord,Show)
  origin = Center (0,0)
  leaf (Center i) = i
  split i (Center j) =  if i == j  then Nothing else Just ( i `sub` j)
  splitPre i  j = (Center i ,(Nothing,Nothing))
  append (Center (i,j) ) (Center (l,m)) =  (Center (i+l,j+m))
  pickSplitN = pickQuadSplit
  chooseTree = chooseQuadTree
  consistent (Right i ) (Left (Center j)) = getQuadrant  i == getQuadrant  j
    where Center o =  origin
  consistent (Right i ) (Right j ) = i == j
  consistent i j = error $ show ("consistent",i,j)
  consistent (Left (Center i)) (Left (Center j)) = i == j



quaditems :: [(Rational,Rational)]
quaditems = [(10,10),(0,10),(0,-10),(-10,-10),(-10,-11),(-20,-10)]
fullQuad = foldl (\g -> uncurry (insertSplit conf g)) empty (zip quaditems [0..])
emptyQuad = scanl delete fullQuad quaditems ++ scanl delete fullQuad (reverse quaditems)

insertMany ::  Predicates a => GiST a b -> [(a,b)] -> [GiST a b]
insertMany g = scanl (\g -> uncurry (insertSplit conf g)) g


addDeleteQuad :: [(Rational,Rational)] -> Bool
addDeleteQuad l = foldl delete (foldl (\g -> uncurry (insertSplit conf g)) empty (zip l [(0::Int)..])) (reverse l) == empty

putScan :: Show a => [a] -> IO ()
putScan = putStrLn  . unlines . fmap show



pointLeft (x,y) (i,j) = x < i
pointRight (x,y) (i,j) = x > i
pointAbove (x,y) (i,j) = y > j
pointBelow (x,y) (i,j) = y < j
pointHoriz (x,y) (i,j) =  y == j
pointVert (x,y) (i,j) =  x == i

getQuadrant :: (Show a ,Fractional a,Ord a)=> (a,a) -> Int
getQuadrant  c
  | pointAbove l c || pointHoriz l c && pointRight l c || pointVert l c = 1
  | pointBelow l c && pointRight l c || pointVert l c = 2
  | pointBelow l c || pointHoriz l c && pointLeft l c = 3
  | pointAbove l c && pointLeft l c = 4
  where Center l = origin


prefixQuad l =  centroid
  where
    centroid = (meanx,meany)
    meanx = sum (fmap fst l ) / fromIntegral (length l)
    meany = sum (fmap snd l ) / fromIntegral (length l)



chooseQuadTree p  (Node (Center pre) _ l) = S.findIndexL ((\(Center i) -> getQuadrant  i == pquad ) .prefix)l
  where pquad = getQuadrant  p

sub (x,y) (l,m) = (x-l,y-m)

pickQuadSplit l =  (Center center,Nothing,quadSplit l)
  where center = prefixQuad (fmap ( either unCenter id . entryPredicate ) $ F.toList l)
        entryOrigin = (fmap (editEntry center  )l)
        unCenter (Center i) = i
        quadSplit l =  fmap  genPrefix $ groupBy (opbi (==) (getQuadrant  . (either unCenter id) .entryPredicate )) $ S.sortBy (comparing entryPredicate)  entryOrigin
        genPrefix j = (Center p ,Nothing ,fmap (editEntry p) j)
          where p = prefixQuad (fmap (either unCenter id . entryPredicate ) $ F.toList j)

editEntry :: Num b => (b,b) -> Entry f (b,b) a -> Entry f (b,b) a
editEntry c (LeafEntry (l,p) ) =  LeafEntry (l,p `sub` c)
editEntry c (NodeEntry (l,Center p)) =  NodeEntry (l,Center $ p `sub` c)


