{-# LANGUAGE StandaloneDeriving,TupleSections,PatternSynonyms,ViewPatterns,FlexibleInstances,DeriveTraversable , DeriveFoldable,DeriveFunctor,DeriveGeneric,TypeFamilies ,FlexibleContexts,ScopedTypeVariables #-}
module Data.GiST.PatriciaTree where

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
instance (Show a,Ord a )=>  Predicates [a] where
  data Node [a]
    = Common [a]
    deriving (Eq,Show,Ord)
  leaf (Common l ) =  l
  split []  (Common [] ) =  Nothing
  split i (Common l)
    | i ==  l = Nothing
    | take (length l) i /= l =   Nothing
    | otherwise = Just $ drop (length l) i
  origin = Common []
  splitPre i (Common j) =  (Common a ,(Common <$> b , Common <$> c))
    where
      (a,(b,c)) = sp i j
      sp [] [] = ([],(Nothing,Nothing))
      sp xs []  = ([],(Just xs,Nothing))
      sp [] xs = ([],(Nothing,Just xs))
      sp (i:xs) (j:ys)
        | i == j = first (i :)  $ sp xs ys
        | otherwise = ([] ,(Just (i:xs), Just (j:ys)))
  append (Common i ) (Common j) = Common ( i ++ j)
  consistent (Left (Common i)) (Left (Common j) ) = i == j
  consistent (Right j ) (Left (Common i)) =  i `L.isInfixOf` j
  consistent (Left (Common i)) (Right j) =  i `L.isInfixOf` j
  consistent  (Right j) (Right i) = i == j
  consistent i j = error (show ("consistent" ,i,j))
  pickSplitN = pickPrefixSplit
  chooseTree  = chooseListTree

commonPrefix ::  Eq e  => [e] -> [e] -> [e]
commonPrefix _ [] = []
commonPrefix [] _ = []
commonPrefix (x:xs) (y:ys)
  | x == y    = x : commonPrefix xs ys
  | otherwise = []

commonPrefixAll :: (Eq e, Foldable f ) => f [e] ->  [e]
commonPrefixAll = F.foldl1 commonPrefix

prefixList :: (Show a,Ord a) => Seq [a] -> [a]
prefixList =  commonPrefixAll

safeHead :: [a] -> Maybe a
safeHead [] = Nothing
safeHead i = Just $ head i

rights  = fmap (\(Right i) -> i) . S.filter isRight
lefts  = fmap (\(Left i) -> i) . S.filter isLeft

chooseListTree p  (Node (Common pre) _ l) = S.findIndexL ((\i -> consistent (Right p) (Left i)) .prefix)l

pickPrefixSplit l =  (center,topValue,quadSplit center l)
  where center = Common $ prefixList (fmap ( either leaf id . entryPredicate )  l)
        entryOriginA  = fmap (editEntryList center  ) l
        topValue = fmap (\(Left i) -> i) $ L.find isLeft entryOriginA
        entryOrigin = rights entryOriginA
        quadSplit centroid l =  fmap  genPrefix $ groupBy (opbi (==) (safeHead . either leaf id .entryPredicate)) $ S.sortBy (comparing entryPredicate) entryOrigin
        genPrefix j = (Common p ,el,er )
          where p = prefixList (fmap (either leaf id . entryPredicate )  j)
                elr =fmap (editEntryList (Common p)) j
                el = fmap (\(Left i) -> i) $ L.find isLeft elr
                er = rights elr


-- editEntryList :: Num b => (b,b) -> Entry f (b,b) a -> Entry f (b,b) a
editEntryList c (LeafEntry (l,p) ) =  case p `split` c of
                                        Just s -> Right $ LeafEntry (l, s )
                                        Nothing -> Left l
editEntryList c (NodeEntry (l,p)) =  Right $ NodeEntry (l,p )


listitems ::  [[Int]]
listitems =  [[],[1,2,3],[6,5],[1,2,3,4],[1,2,3,4,5],[1,2,3,4,6],[1,2,3,4,5,9],[6,4],[9,4],[9,2]]
fullList = foldl (\g -> uncurry (insertSplit conf g)) empty (zip listitems [0..])
emptyList = scanl delete fullList (listitems) ++  scanl delete fullList (reverse listitems)

addDeleteList :: [[Int]] -> Bool
addDeleteList l = foldl delete (foldl (\g -> uncurry (insertSplit conf g)) empty (zip l [0..])) (reverse l) == (empty :: GiST [Int] Int)
