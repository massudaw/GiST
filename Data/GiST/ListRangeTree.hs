{-# LANGUAGE StandaloneDeriving,TupleSections,PatternSynonyms,ViewPatterns,FlexibleInstances,DeriveTraversable , DeriveFoldable,DeriveFunctor,DeriveGeneric,TypeFamilies ,FlexibleContexts,ScopedTypeVariables #-}
module Data.GiST.ListRangeTree where

import  Data.GiST.SPGiST
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
-- List Predicate  --
---------------------

intersect (min1,max1) (min2,max2) = (min1 <= max2) && (max1 >= min2)

between :: Ord a => a -> a -> a -> Bool
between a min max = (a >= min) && (a <= max)

instance (Show a,Ord a )=>  Predicates [a] where
  data Node [a]
    = Common [a] ([a],[a])
    deriving (Eq,Show,Ord)
  leaf (Common l _) =  l
  origin = Common [] ([],[])
  splitPrefix i (Common l r)
    | i /= l && take (length l) i == l && not (L.null i) =  Right $ drop (length l) i
  splitPrefix i (Common j r) =  Left (Common a r,(flip Common r <$> b , flip Common r<$> c))
    where
      (a,(b,c)) = sp i j
      sp [] [] = ([],(Nothing,Nothing))
      sp xs []  = ([],(Just xs,Nothing))
      sp [] xs = ([],(Nothing,Just xs))
      sp (i:xs) (j:ys)
        | i == j = first (i :)  $ sp xs ys
        | otherwise = ([] ,(Just (i:xs), Just (j:ys)))
  append (Common i r) (Common j rj) = Common ( i ++ j) rj
  consistent (Left (Common i ri )) (Left (Common j rj ) ) = i == j && ri `intersect` rj
  consistent (Right j ) (Left (Common i (rj1,rj2) )) =  i `L.isPrefixOf` j && all id (zipWith3 between (L.drop (L.length i ) j ) rj1 rj2)
  consistent (Left (Common i (rj1,rj2))) (Right j) =  i `L.isPrefixOf` j && all id (zipWith3 between (L.drop (L.length i ) j ) rj1 rj2)
  consistent  (Right j) (Right i) = i == j
  consistent i j = error (show ("consistent" ,i,j))
  pickSplitN = pickPrefixSplit
  chooseSubTree  = chooseListTree

minmaxPrefix ::  Ord e  => [(e,e,Int)] -> [(e,e,Int)] -> [(e,e,Int)]
minmaxPrefix xs [] = xs
minmaxPrefix [] xs = xs
minmaxPrefix [] [] = []
minmaxPrefix (x@(x1,x2,xc):xs) (y@(y1,y2,yc):ys)
  = (min x1 y1 , max x2 y2,xc+yc) : minmaxPrefix xs ys


prefixList :: (Show a , Ord a) => Seq [a] -> Node [a]
prefixList il =   stripCommon . F.foldl1 (\i j ->  minmaxPrefix i j)  . dupPrefix $ il
  where dupPrefix :: Seq [a] -> Seq [(a,a,Int)]
        dupPrefix = fmap (fmap (\i -> (i,i,1)))
        lil = length il
        stripCommon l = Common  (fmap (\(i,_,_) -> i ) c) (unzip $ fmap (\(i,j,_) -> (i,j)) r)
          where (c,r)= break (\(i,j,c) -> i /= j  || c /= lil)  l

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead i = Just $ head i

rights  = fmap (\(Right i) -> i) . S.filter isRight
lefts  = fmap (\(Left i) -> i) . S.filter isLeft

chooseListTree p  v (Node (pre) _ l) = maybe (Left emptyLeaf)Right $ S.findIndexL ((\i -> consistent (Right p) (Left i)) .prefix)l
  where (Right i ) = splitPrefix p  pre
        emptyLeaf = Leaf  (Common i ([],[])) (Just v) S.empty


pickPrefixSplit l =  (center,topValue,quadSplit center l)
  where center = prefixList (fmap ( either leaf id . entryPredicate )  l)
        entryOriginA  = fmap (editEntryList center  ) l
        topValue = fmap (\(Left i) -> i) $ L.find isLeft entryOriginA
        entryOrigin = rights entryOriginA
        quadSplit centroid l =  fmap  genPrefix $ groupBy (opbi (==) (safeHead . either leaf id .entryPredicate)) $ S.sortBy (comparing entryPredicate) entryOrigin
        genPrefix j =  (p ,el,er )
          where p = prefixList (fmap (either leaf id . entryPredicate )  j)
                elr =fmap (editEntryList (p)) j
                el = fmap (\(Left i) -> i) $ L.find isLeft elr
                er = rights elr

leafPrefix (Common i _ )  = i

-- editEntryList :: Num b => (b,b) -> Entry f (b,b) a -> Entry f (b,b) a
editEntryList c (LeafEntry (l,p) ) =  case p `splitPrefix` c of
                                        Right s -> Right $ LeafEntry (l, s )
                                        Left _ -> Left l
editEntryList c (NodeEntry (l,p)) =  Right $ NodeEntry (l,p )



listitems ::  [[Int]]
-- listitems =  [[1,2,3],[6,5],[1,2,3,4],[1,2,3,4,5],[1,2,3,4,6],[1,2,3,4,5,9],[6,4],[9,4],[9,2]]
-- listitems =  [[1,2,3],[6,5],[1,2,3,4],[1,2,3,4,5],[1,2,3,4,6],[1,2,3,4,5,9],[6,4],[9,4],[9,2]]
-- listitems = [[0],[1],[2],[3],[4],[],[]]
-- listitems = [[-46],[-46,0],[0],[1],[2]]
-- listitems = [[-84,0],[-84,1],[-84,2],[0],[-84,3],[-84,4]]
-- listitems = [[0],[1],[2],[3],[0,0]]
listitems = [[0],[1],[2],[3],[0,1]]
fullList = scanl (\g -> uncurry (insertSplit conf g)) empty (zip listitems [0..])
emptyList = scanl delete (last fullList) (listitems) ++ scanl delete (last fullList) (reverse listitems)
searchList = fmap (\(i,v) -> (i,v,   [v]== search i (last fullList ),   search i (last fullList )) ) (L.nubBy (\i j -> fst i == fst j) $ reverse $ zip listitems [(0::Int) ..])

addDeleteList :: [[Int]] -> Bool
addDeleteList l = foldl delete (foldl (\g -> uncurry (insertSplit conf g)) empty (zip l [0..])) (reverse l) == (empty :: GiST [Int] Int)

addSearch :: [[Int]] -> Bool
addSearch l = all (\(i,v) -> [v] == search i (foldl (\g -> uncurry (insertSplit conf g)) empty (zip l [(0::Int)..]))) (L.nubBy (\i j -> fst i == fst j) $ reverse $ zip l [(0::Int) ..])

putScan :: Show a => [a] -> IO ()
putScan = putStrLn  . unlines . fmap show
