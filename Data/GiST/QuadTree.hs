{-# LANGUAGE StandaloneDeriving,TupleSections,PatternSynonyms,ViewPatterns,FlexibleInstances,DeriveTraversable , DeriveFoldable,DeriveFunctor,DeriveGeneric,TypeFamilies ,FlexibleContexts,ScopedTypeVariables #-}
module Data.GiST.QuadTree where

import Data.GiST.SPGiST
import Data.Tuple
import Data.Either (isRight,isLeft)
import Control.Monad
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
  splitPrefix i (Center j) =  if i == j  then Left (Center i ,(Nothing,Nothing)) else Right ( i `sub` j)
  append (Center (i,j) ) (Center (l,m)) =  (Center (i+l,j+m))
  pickSplitN = pickQuadSplit
  chooseSubTree = chooseQuadTree
  consistent (Right i ) (Left (Center j)) = getQuadrant  i == getQuadrant  j
    where Center o =  origin
  consistent (Right i ) (Right j ) = i == j
  consistent i j = error $ show ("consistent",i,j)
  consistent (Left (Center i)) (Left (Center j)) = i == j



quaditems :: [(Rational,Rational)]
-- quaditems = [(10,10),(0,10),(0,-10),(-10,-10),(-10,-11),(-20,-10),(10,11),(10,11),(10,11),(1,2)]
-- quaditems = read "[(0 % 1,1 % 1),(0 % 1,2 % 1),(0 % 1,3 % 1),(0 % 1,4 % 1),(1 % 1,0 % 1)]"
-- quaditems = read "[(0 % 1,1 % 1),(0 % 1,2 % 1),(0 % 1,3 % 1),(1 % 1,0 % 1),(0 % 1,9 % 1)]"
--quaditems = read "[(0 % 1,1 % 1),(0 % 1,2 % 1),(0 % 1,4 % 1),(0 % 1,5 % 1),(0 % 1,3 % 1)]"
quaditems = read "[(0 % 1,1 % 1),(0 % 1,2 % 1),(1 % 1,0 % 1),(0 % 1,3 % 1),((-3966458116216) % 2234476581439,55546802161 % 628276439727),((-2581941493792) % 6148082380399,2 % 1)]"
--quaditems = read "[(0 % 1,1 % 1),(1658585082895 % 4719792246136,0 % 1),(0 % 1,2 % 1),(0 % 1,3 % 1),(0 % 1,36949039167886 % 9748837367237),((-174045663266) % 548381067121,1 % 1)]"
--quaditems = read "[(0 % 1,1 % 1),(0 % 1,0 % 1),(0 % 1,2 % 1),(0 % 1,3 % 1),(0 % 1,4 % 1),(0 % 1,5 % 1)]"
fullQuad = scanl (\g -> uncurry (insertSplit conf g)) empty (zip quaditems [0..])
emptyQuad = scanl delete (last fullQuad) (quaditems) ++ scanl delete (last fullQuad) (reverse quaditems)
searchQuad = fmap (\(i,v) -> (i,v,   [ v] == searchKey i (last fullQuad)) ) (L.nubBy (\i j -> fst i == fst j) $ reverse $ zip quaditems [(0::Int) ..])

insertMany ::  Predicates a => GiST a b -> [(a,b)] -> [GiST a b]
insertMany g = scanl (\g -> uncurry (insertSplit conf g)) g


addDeleteQuad :: [(Rational,Rational)] -> Bool
addDeleteQuad l = foldl delete (foldl (\g -> uncurry (insertSplit conf g)) empty (zip l [(0::Int)..])) (reverse l) == empty

addSearch :: [(Rational,Rational)] -> Bool
addSearch l = all (\(i,v) -> [v] == searchKey i (foldl (\g -> uncurry (insertSplit conf g)) empty (zip l [(0::Int)..]))) (L.nubBy (\i j -> fst i == fst j) $ reverse $ zip l [(0::Int) ..])

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



chooseQuadTree p  v (Node (Center pre) _ l) = maybe (Left $ Leaf  (Center (p `sub` pre)) (Just v) S.empty ) Right $ S.findIndexL ((\(Center i) -> getQuadrant  i == pquad ) .prefix)l
  where pquad = getQuadrant  (p `sub` pre)

sub (x,y) (l,m) = (x-l,y-m)

pickQuadSplit l =  (Center center,join $ (\(_,v,_) -> v) . S.index ql <$> S.findIndexL (\(i,_,_) -> i ==origin) ql ,fmap (\(i,j,k) -> if i== origin then (i,Nothing,k) else (i ,j,k)) ql)
  where center = prefixQuad (fmap ( either unCenter id . entryPredicate ) $ F.toList l)
        ql = quadSplit l
        entryOrigin = (fmap (editEntry center  )l)
        unCenter (Center i) = i
        quadSplit l =  fmap  genPrefix $ groupBy (opbi (==) (getQuadrant  . (either unCenter id) .entryPredicate )) $ S.sortBy (comparing entryPredicate)  entryOrigin
        genPrefix j
          | length j == 1 && isLeaf (head $ F.toList j) = (Center p,Just (leafValue $  head $ F.toList j),S.empty)
          | otherwise = (Center p ,leafValue . S.index j <$> S.findIndexL ((==p).either unCenter id .entryPredicate) j ,fmap (editEntry p) (S.filter ((/=p). either unCenter id .entryPredicate)j))
          where p = prefixQuad (fmap (either unCenter id . entryPredicate ) $ F.toList j)

isLeaf (LeafEntry i) = True
isLeaf _ = False
leafValue (LeafEntry (l,p)) =  l

editEntry :: Num b => (b,b) -> Entry f (b,b) a -> Entry f (b,b) a
editEntry c (LeafEntry (l,p) ) =  LeafEntry (l,p `sub` c)
editEntry c (NodeEntry (l,Center p)) =  NodeEntry (l,Center $ p `sub` c)


