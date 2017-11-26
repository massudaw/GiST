{- |
Module      :  GiST
Copyright   :  (c) Mihail Bogojeski, Alexander Svozil
License     :  GPL

Maintainer  :  mihailbogojeski@gmail.com
Stability   :  experimental
Portability :  portable

The implementation of the basic GiST operations. The behaviour
of the operations is largely influenced by the predicate used, allowing the GiST to behave
like a different type of balanced search tree for a different predicate. Although the operations
are influenced by the predicate, it is always ensured that the tree stays balanced after an
insertion or deletion, regardless of the predicate used. It is also recommended that the minimum
and maximum fill factor for the tree are constant throughout the whole program to ensure optimal
behaviour
-}


{-# LANGUAGE MultiParamTypeClasses
    ,FlexibleInstances
    ,ScopedTypeVariables
    ,FlexibleContexts
    #-}

module Data.GiST.GiST
    (
        -- ** Types
        GiST
        ,Penalty(..)
        ,Entry(..)
        ,Predicates(..)
        ,LeafEntry,NodeEntry
        ,leafValue
        ,leafPred
        ,entryPredicate
        ,union
        ,getEntries
        -- ** GiST operations
    ,query,queryL,update,alter ,search,searchKey, insert,insertL, delete, empty,  getData, size,putScan,bounds
    ) where

import Data.GiST.Types
import Control.Monad (join)
import qualified Data.Text.IO as TIO
import qualified Data.Text as T
import Data.List (null,minimumBy)
import Data.Ord (comparing)
import GHC.Stack
import Debug.Trace
import Data.Monoid
import qualified Data.Sequence as S
import qualified Data.Foldable as F
import Data.Sequence ( Seq)

query :: Predicates p  => Query p  -> GiST p a -> [(a,p)]
query p es     = fmap (\(v,_,l) -> (v,l)) $ queryL p es

queryL :: Predicates p  => Query p  -> GiST p a -> [LeafEntry p a ]
queryL p (Leaf _ es)     =  F.toList $ S.filter (\(_,n,l) ->  match p (Left n) && match p  (Right l)) es
queryL p (Node pn es)
  = concat $ fmap (\e -> if match p  (Left $ nodePredicate e) then queryL p e else [])  es
queryL _ (Node _ Empty)     =[]




firstL f ~(i,j,k) = (f i,j,k)
first f ~(i,j) = (f i,j)

unNode (Node _ e ) = e


update :: Predicates p  => p  -> (a -> a) -> GiST p a -> GiST p a
update p f (Leaf pn  es) = Leaf pn $(\e@(v,n,l) ->  if consistent (Right p ) (Left n) && consistent (Right p) (Right  l) then firstL f e else e ) <$> es
update _ f (Node p Empty) = Node p Empty
update p f (Node pn (e:<es))
    |consistent (Right p) (Left $ nodePredicate e) = Node pn $ (update p f e ):< unNode (update p f (Node pn es) )
    |otherwise                  = Node pn (e :< unNode (update p f (Node pn es)))

alter :: Predicates p  => Query p  -> (a -> a) -> GiST p a -> GiST p a
alter p f (Leaf pn es)     = Leaf pn $(\e@(v,n,l) -> if match p (Left  n) && match p (Right $ l) then firstL f e else e ) <$> es
alter _ f (Node pn Empty)     =Node pn Empty
alter p f (Node pn (e:<es))
    |match p (Left $ nodePredicate e) = Node pn $ alter p f e :< unNode (alter p f (Node pn es) )
    |otherwise                  = Node pn (e :< unNode (alter p f (Node pn es)))





-- | Searches the GiST for leaf nodes that satisfy the given search predicate
search  :: Predicates p  => p  -> GiST p a -> [a]
search p = fmap fst . searchKey p

-- | Inserts an entry into the tree, rebalancing the tree if necessary.
-- Rebalancing is done to satisfy the minimum and maximum fill factor
-- of the tree (represented as an integer tuple)
insert  :: Predicates p  => (a, p) -> (Int, Int) -> GiST p a -> GiST p a
insert (x,l) = insertL (x,bound l,l)

insertL  :: Predicates p  => LeafEntry p a -> (Int, Int) -> GiST p a -> GiST p a
insertL (toIns, n , pred) (min,max) gi@(Node pn es)
        |length newEs <= max || not ( null $ search pred gi )  =  Node newP newEs
        |otherwise              = uncurry Node splitS
            -- The new entries after inserting
    where   newEs = case insertSubtree of
                        Keep newSub -> S.adjust (const newSub) ix es
                        Split split -> deleteAt ix es <> snd split
            newP = (merge pn (bound pred))
            -- The optimal subtree to insert into
            (minSubtree ,ix)= chooseSubtree es pred
            -- The changed (and additional) subtree after insert
            insertSubtree = insertAndSplit minSubtree (min,max) (toIns,n,pred)
            -- The split of the node entries (in case of overpopulation)
            splitS =  pickSplit $ Node newP  newEs

insertL (toIns, n,p) (min,max) (Leaf pn es)
        |not $ null $ search p (Leaf pn es) = Leaf newP (fmap (\(i,n,j) -> if consistent (Right j ) (Left n) && consistent (Right j) (Right p) then (toIns ,n,j) else  (i,n,j) )es)
        |length newEs <= max    = Leaf newP newEs
        |otherwise              = uncurry Node splitS
            -- The new entries after insert
    where   newEs = (toIns, n,p):<es
            newP = merge  pn (bound p )
            -- The split of the node entries (in case of overpopulation)
            splitS =  pickSplit $ Leaf newP newEs

-- | Deletes a leaf entry from the tree, rebalancing the tree if necessary.
-- Rebalancing is done to satisfy the minimum and maximum fill factor
-- of the tree (represented as an integer tuple)
delete  :: Predicates p  => p  -> (Int, Int) -> GiST p a -> GiST p a
delete p (min,max) (Node pn es)
        | length newEs == 0 = insertMultiple toAdd empty (min,max)
        | length newEs == 1 = insertMultiple toAdd (head $ F.toList newEs) (min,max)
        | otherwise        = insertMultiple toAdd (Node (union (fmap (nodePredicate )newEs)) newEs) (min, max)
            -- The new entries after delete without Null entries
    where   newEs = S.filter (not.isNull) (fmap fst delNodes)
            -- The propagated entries to add
            toAdd = join (fmap snd delNodes)
            -- The entries after delete
            delNodes =  fmap (\e -> if (consistent (Right p) (Left $nodePredicate e))
                            then (deleteAndCondense e (min,max) p)
                            else (e,Empty)
                        )es

delete p (min,max) (Leaf pn es) = Leaf (union $ fmap (\(_,n,_) -> n) out) out
  where out =  S.filter (\(v,n,l) ->  not $ consistent (Right p)  (Right l)) es

-- | Create a new empty GiST
empty :: Predicates p => GiST p a
empty = Leaf origin S.empty

data Balance p a
  = Split (Node p ,Seq (GiST p a))
  | Keep (GiST p a)


-- | A helper function that propagates insertion through the subtrees and splits when necessary.
-- If the node is overpopulated after the insertion, the node is split into
-- two smaller nodes which are then added to the parent
insertAndSplit :: Predicates p  => NodeEntry p a -> (Int,Int) -> LeafEntry p a -> Balance p a
insertAndSplit (Node p es) (min,max) (toIns,n,pred)
            |length newEs <= max  =  Keep (Node   newIdx  newEs)
            |otherwise = Split $ splitS
                -- The new entries after insert
    where   newEs = case insertSubtree of
                      Keep newSub -> S.adjust (const newSub) idx es
                      Split split -> deleteAt idx es <> snd  split
            -- The optimal subtree to insert into
            (minSubtree ,idx)= chooseSubtree es pred
            newIdx = merge (bound pred) (p)
            -- The changed (and additional) subtree after insert
            insertSubtree = insertAndSplit minSubtree (min,max) (toIns,n,pred)
            -- The split of the node entries (in case of overpopulation)
            splitS =  pickSplit $ Node  newIdx newEs

insertAndSplit (Leaf p es) (min,max) (toIns,n,pred)
            |not $ null $ search pred (Leaf p es) = Keep (Leaf newP (fmap (\(i,n,j) -> if consistent (Right j) (Left n) && consistent (Right j) (Right pred) then (toIns ,n,j) else  (i,n,j) )es))
            |length newEs <= max  = Keep (Leaf newP  newEs)
            |otherwise = Split  splitS
            -- The optimal subtree to insert into
    where   newEs = ((toIns,n,pred) :< es)
            newP = (merge (bound pred ) p)
            -- The split of the node entries (in case of overpopulation)
            splitS =  pickSplit $ Leaf newP  newEs


-- A helper function that propagates deletion through the subtrees and condenses.
-- If an internal node is underpopulated after deletion, the node and all it's subnodes are removed
-- and all their leaf entries are stored for reinsertion. The deletion is then propagated to the parent
-- of the node
deleteAndCondense :: Predicates p  => NodeEntry p a -> (Int,Int) -> p  -> (NodeEntry p a, Seq (LeafEntry p a))
deleteAndCondense node@(Node pred es) (min, max) p
        |length newEs < min = (empty , S.filter (not . consistent (Right p) .Right .leafPred ) (getEntriesS node))
        |otherwise          = (Node (union $ fmap nodePredicate newEs) newEs , toAdd)
            -- The new entries after delete without Null entries
    where   newEs = S.filter (not.isNull) (fmap fst delNodes)
            -- The propagated entries to add
            toAdd = join (fmap snd delNodes)
            -- The entries after delete
            delNodes =  fmap (\e -> if (consistent (Right p) (Left $ nodePredicate e))
                            then (deleteAndCondense e (min,max) p)
                            else (e,Empty)) es
-- If a leaf is underpopulated after deletion, the leaf is removed and all its entries are
-- stored for reinsertion. The deletion is then propagated to the parent of the node
deleteAndCondense (Leaf pred es) (min, max) p
    |length newEs < min = (empty, newEs)
    |otherwise          = (Leaf ( union $ fmap leafNode newEs) newEs,Empty)
                -- The new entries after delete without Null entries
      where   newEs = S.filter (\(v,n,l)-> not (  consistent (Right p) (Right l))) es



-- Inserts multiple entries into a GiST
insertMultiple :: (Predicates p ) => Seq (LeafEntry p a) -> GiST p a -> (Int,Int) -> GiST p a
insertMultiple es gist (min,max) = F.foldl' (\ gist e-> insertL  e (min,max) gist) gist  es




-- Takes an entry and extracts the GiST from it


-- Checks if an entry contains a Null GiST
isNull :: NodeEntry p a -> Bool
isNull (Leaf p Empty) = True
isNull _ = False


-- Returns all the entries stored in a GiST
getEntries :: GiST p a -> [LeafEntry p a]
getEntries (Node _ es) = concat [getEntries sub | sub <- F.toList es]
getEntries (Leaf _ es) = F.toList es

getEntriesS :: GiST p a -> Seq (LeafEntry p a)
getEntriesS (Node _ es) = join $ fmap getEntriesS es
getEntriesS (Leaf _ es) = es



-- | Returns all the data stored in a GiST
getData :: GiST p a -> [a]
getData gist = fmap leafValue $ getEntries gist

-- | Return the number of values in a GiST
size :: GiST p a -> Int
size gist = length $ getEntries gist

bounds :: GiST p a -> Node p
bounds (Leaf i  _ ) = i
bounds (Node i  _ ) = i


putScan :: Show a => [a] -> IO ()
putScan = putStrLn  . unlines . fmap show
