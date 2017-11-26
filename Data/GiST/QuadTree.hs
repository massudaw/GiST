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

mean :: Fractional a => Node (a,a) -> (a,a)
mean (Center (x,y) ix)
  | ix == 0 = (x,y)
  | otherwise  = (x/fromIntegral ix,y/fromIntegral ix)

instance (Show a,Fractional a ,Ord a ,Num a) => Predicates (a,a) where
  data Node (a,a) = Center (a,a) Int deriving(Eq,Ord,Show)
  origin = Center (0,0) 0
  leaf  = mean
  splitPrefix i c@(Center _ ix ) =  if i == mean c  then Left (Center (mult (fromIntegral ix ) i) ix,(Nothing,Nothing)) else Right ( i `sub` mean c )
  append oi (Center (l,m) ij)
    =  Center (addt (mult (fromIntegral ij )(mean oi )) (l,m)) ij
  add = flip const
  pickSplitN = pickQuadSplit
  chooseSubTree = chooseQuadTree
  consistent (Right i ) (Left c) = getQuadrant  i == getQuadrant  (mean c)
  consistent (Right i ) (Right j ) = i == j
  consistent (Left i ) (Left (j )) = mean i == mean j
  consistent i j = error $ show ("consistent",i,j)



quaditems :: [(Rational ,Rational)]
-- quaditems = [(10,10),(0,10),(0,-10),(-10,-10),(-10,-11),(-20,-10),(10,11),(10,11),(10,11),(1,2)]
-- quaditems = read "[(0 % 1,1 % 1),(0 % 1,2 % 1),(0 % 1,3 % 1),(0 % 1,4 % 1),(1 % 1,0 % 1)]"
-- quaditems = read "[(0 % 1,1 % 1),(0 % 1,2 % 1),(0 % 1,3 % 1),(1 % 1,0 % 1),(0 % 1,9 % 1)]"
--quaditems = read "[(0 % 1,1 % 1),(0 % 1,2 % 1),(0 % 1,4 % 1),(0 % 1,5 % 1),(0 % 1,3 % 1)]"
--quaditems = read "[(0 % 1,1 % 1),(0 % 1,2 % 1),(1 % 1,0 % 1),(0 % 1,3 % 1),((-3966458116216) % 2234476581439,55546802161 % 628276439727),((-2581941493792) % 6148082380399,2 % 1)]"
--quaditems = read "[(0 % 1,1 % 1),(1658585082895 % 4719792246136,0 % 1),(0 % 1,2 % 1),(0 % 1,3 % 1),(0 % 1,36949039167886 % 9748837367237),((-174045663266) % 548381067121,1 % 1)]"
--quaditems = read "[(0 % 1,1 % 1),(0 % 1,0 % 1),(0 % 1,2 % 1),(0 % 1,3 % 1),(0 % 1,4 % 1),(0 % 1,5 % 1)]"
quaditems  = read "[(0 % 1,1 % 1),(0 % 1,2 % 1),(0 % 1,3 % 1),(0 % 1,10 % 1),((-1) % 1,0 % 1),(0 % 1,0 % 1)]"
fullQuad = scanl (\g -> uncurry (insertSplit conf g)) empty (zip quaditems [0..])
emptyQuad = scanl delete (last fullQuad) (quaditems) ++ scanl delete (last fullQuad) (reverse quaditems)
searchQuad = fmap (\(i,v) -> (i,v,search i (last fullQuad),   [ v] == search i (last fullQuad)) ) (L.nubBy (\i j -> fst i == fst j) $ reverse $ zip quaditems [(0::Int) ..])

-- insertMany ::  Predicates a => GiST a b -> [(a,b)] -> [GiST a b]
insertMany g = scanl (\g -> uncurry (insertSplit conf g)) g


addDeleteQuad :: [(Rational,Rational)] -> Bool
addDeleteQuad l = foldl delete (foldl (\g -> uncurry (insertSplit conf g)) empty (zip l [(0::Int)..])) (reverse l) == empty

addSearch :: [(Rational,Rational)] -> Bool
addSearch l = all (\(i,v) -> [v] == search i (foldl (\g -> uncurry (insertSplit conf g)) empty (zip l [(0::Int)..]))) (L.nubBy (\i j -> fst i == fst j) $ reverse $ zip l [(0::Int) ..])

putScan :: Show a => [a] -> IO ()
putScan = putStrLn  . unlines . fmap show



pointLeft  (i,j) = 0 < i
pointRight  (i,j) = 0 > i
pointAbove  (i,j) = 0 > j
pointBelow  (i,j) = 0 < j
pointHoriz  (i,j) =  0 == j
pointVert  (i,j) =  0 == i

getQuadrant :: (Show a ,Fractional a,Ord a)=> (a,a) -> Int
getQuadrant  c
  | pointAbove  c || pointHoriz  c && pointRight  c || pointVert  c = 1
  | pointBelow  c && pointRight  c || pointVert  c = 2
  | pointBelow  c || pointHoriz  c && pointLeft  c = 3
  | pointAbove  c && pointLeft  c = 4


prefixQuad :: (Show a ,Num a) => [Either (Node (a,a)) (a,a)] -> Node (a,a)
prefixQuad l =   Center centroid c
  where
    centroid = (meanx,meany)
    xc (Right (x,_)) = x
    xc (Left (Center (x,_) _ )) = x
    yc (Right (_,y)) = y
    yc (Left (Center (_,y) _)) = y
    cc (Right (_,_)) = 1
    cc (Left (Center (_,_) c) )= c
    meanx = sum (fmap xc l)
    meany = sum (fmap yc l)
    c = sum (fmap cc l)



chooseQuadTree p  v (Node c _ l) = maybe (Left $ Leaf  (Center (p `sub` mean c ) 1 ) (Just v) S.empty ) Right $ S.findIndexL ((\i -> getQuadrant  (mean i) == pquad ) .prefix) l
  where pquad = getQuadrant  (p `sub` mean c )

addt :: Num a => (a ,a) -> (a,a) -> (a,a)
addt (x,y) (l,m) = (x+l,y+m)
sub :: Num a => (a ,a) -> (a,a) -> (a,a)
sub (x,y) (l,m) = (x-l,y-m)

pickQuadSplit l =  (center ,join $ (\(_,v,_) -> v) . S.index ql <$> S.findIndexL (\(i,_,_) -> mean i == leaf origin) ql ,fmap (\(i,j,k) -> if mean i== leaf origin then (i,Nothing,k) else (i ,j,k)) ql)
  where center = prefixQuad (fmap entryPredicate  $ F.toList l)
        ql = quadSplit l
        entryOrigin = fmap (editEntry center) l
        quadSplit l =  fmap  genPrefix $ groupBy (opbi (==) (getQuadrant  . (either mean id) .entryPredicate )) $ S.sortBy (comparing entryPredicate)  entryOrigin
        genPrefix j
          | length j == 1 && isLeaf (head $ F.toList j) = (p,Just (leafValue $  head $ F.toList j),S.empty)
          | otherwise = (p ,leafValue . S.index j <$> S.findIndexL ((==mean p).either mean id .entryPredicate) j ,fmap (editEntry p) (S.filter ((/=mean p). either mean id .entryPredicate)j))
          where p = prefixQuad (fmap  entryPredicate  $ F.toList j)

isLeaf (LeafEntry i) = True
isLeaf _ = False
leafValue (LeafEntry (l,p)) =  l

mult i (a,b) = (i*a,i*b)
editEntry :: (Fractional b,Num b) => Node (b,b) -> Entry f (b,b) a -> Entry f (b,b) a
editEntry c (LeafEntry (l,p) ) =  LeafEntry (l,p `sub` mean c)
-- editEntry c (NodeEntry (l,Center p ix )) =  NodeEntry (l,Center  (p `sub` (mult (fromIntegral ix) $  mean c)) ix)


