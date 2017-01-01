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
        ,entryPredicate
        ,union
        ,getEntries
        -- ** GiST operations
    ,query,update,alter ,search,searchKey, insert, delete, empty,  getData, size
    ) where

import Data.GiST.Types
import Control.Monad (join)
import qualified Data.Text.IO as TIO
import qualified Data.Text as T
import Data.List (null,minimumBy)
import Data.Ord (comparing)
import GHC.Stack
import Data.Monoid
import qualified Data.Sequence as S
import qualified Data.Foldable as F
import Data.Sequence ( Seq)

-- | Searches the GiST for leaf nodes that satisfy the given search predicate
searchKey  :: Predicates p  => p  -> GiST p a -> [(a, p)]
searchKey  p (Leaf es)     = F.toList $ S.filter (consistent (Right p) . Right . snd ) es
searchKey  p (Node (e:< es)) =
        if consistent (Right p) (Left $ snd e)
          then searchKey p (fst e) <> (searchKey p (Node es))
          else searchKey p (Node es)
searchKey _ (Node Empty) = []

treePred ::  (GiST p a , Node p)  -> Either (Node p) p
treePred e = Left (snd e)

query :: Predicates p  => Query p  -> GiST p a -> [(a,p)]
query p (Leaf es)     = F.toList $ S.filter (match p . Right .snd) es
query p (Node (e:<es))
    |match p  (treePred e) = (query p (fst e)) <> (query p (Node es))
    |otherwise                  = query p (Node es)
query _ (Node Empty)     =[]



first f ~(i,j) = (f i,j)

unNode (Node e ) = e

update :: Predicates p  => p  -> (a -> a) -> GiST p a -> GiST p a
update p f (Leaf es)     = Leaf $(\e -> if consistent (Right p) (Right $ snd e) then first f e else e ) <$> es
update _ f (Node Empty)     =Node Empty
update p f (Node (e:<es))
    |consistent (Right p) (Left $ snd e) = Node $ (update p f (fst e) ,snd e):< unNode (update p f (Node es) )
    |otherwise                  = Node (e :< unNode (update p f (Node es)))

alter :: Predicates p  => Query p  -> (a -> a) -> GiST p a -> GiST p a
alter p f (Leaf es)     = Leaf $(\e -> if match p (Right $ snd e) then first f e else e ) <$> es
alter _ f (Node Empty)     =Node Empty
alter p f (Node (e:<es))
    |match p (treePred e) = Node $ (alter p f (fst e) ,snd e):< unNode (alter p f (Node es) )
    |otherwise                  = Node (e :< unNode (alter p f (Node es)))





-- | Searches the GiST for leaf nodes that satisfy the given search predicate
search  :: Predicates p  => p  -> GiST p a -> [a]
search p = fmap fst . searchKey p

-- | Inserts an entry into the tree, rebalancing the tree if necessary.
-- Rebalancing is done to satisfy the minimum and maximum fill factor
-- of the tree (represented as an integer tuple)
insert  :: Predicates p  => LeafEntry p a -> (Int, Int) -> GiST p a -> GiST p a
insert (toIns, pred) (min,max) (Node es)
        |not $ null $ search pred (Node es) = Node es
        |length newEs <= max   =  Node newEs
        |otherwise              = Node $ S.fromList [(Node $  fmap unNodeEntry es1, p1 )
                                                    ,(Node $ fmap unNodeEntry es2, p2 )]
            -- The new entries after inserting
    where   newEs = case insertSubtree of
                        Right newSub -> S.adjust (const newSub) ix es
                        Left split -> notMinTree <> S.fromList [fst split,snd split]
            -- The optimal subtree to insert into
            (minSubtree ,~(notMinTree,ix))= chooseSubtree es (toIns,pred)
            -- The changed (and additional) subtree after insert
            insertSubtree = insertAndSplit minSubtree (min,max) (toIns,pred)
            -- The split of the node entries (in case of overpopulation)
            ((p1,es1),(p2,es2)) =  pickSplit $ fmap NodeEntry newEs

insert (toIns, p) (min,max) (Leaf es)
        |not $ null $ search p (Leaf es) = Leaf es
        |length newEs <= max    = Leaf newEs
        |otherwise              = Node $ S.fromList [(Leaf $ fmap unLeafEntry es1,p1 )
                                                    ,(Leaf $ fmap unLeafEntry es2, p2 )]
            -- The new entries after insert
    where   newEs = (toIns, p):<es
            -- The split of the node entries (in case of overpopulation)
            ((p1,es1),(p2,es2)) =  pickSplit $ fmap LeafEntry newEs

-- | Deletes a leaf entry from the tree, rebalancing the tree if necessary.
-- Rebalancing is done to satisfy the minimum and maximum fill factor
-- of the tree (represented as an integer tuple)
delete  :: Predicates p  => p  -> (Int, Int) -> GiST p a -> GiST p a
delete p (min,max) (Node es)
        | length newEs == 0 = insertMultiple toAdd empty (min,max)
        | length newEs == 1  = insertMultiple toAdd (makeRoot $ head $ F.toList newEs) (min,max)
        | otherwise          = insertMultiple toAdd (Node newEs) (min, max)
            -- The new entries after delete without Null entries
    where   newEs = S.filter (not.isNull) (fmap fst delNodes)
            -- The propagated entries to add
            toAdd = join (fmap snd delNodes)
            -- The entries after delete
            delNodes =  fmap (\e -> if (consistent (Right p) (Left $ snd e))
                            then (deleteAndCondense e (min,max) p)
                            else (e,Empty)
                        )es

delete p (min,max) (Leaf es) = Leaf $ S.filter ( consistent (Right p) . Right . snd ) es

-- | Create a new empty GiST
empty :: GiST p a
empty = Leaf Empty
  {-
-- | Loads a GiST from file
load :: (Read a, Read p ) => FilePath -> IO (GiST p a)
load f = do s <- TIO.readFile f
            return (read $ T.unpack s)

-- | Saves the GiST to file
save :: (Show a, Show p ) => GiST p a -> FilePath -> IO ()
save gist f = TIO.writeFile f $ T.pack (show gist)
-}



-- | A helper function that propagates insertion through the subtrees and splits when necessary.
-- If the node is overpopulated after the insertion, the node is split into
-- two smaller nodes which are then added to the parent
insertAndSplit :: Predicates p  => NodeEntry GiST p a -> (Int,Int) -> LeafEntry p a -> Either (NodeEntry GiST p a, NodeEntry GiST p a) (NodeEntry GiST p a)
insertAndSplit (Node es,p) (min,max) (toIns,pred)
            |length newEs <= max  =  Right (Node newEs,union $ fmap treePred newEs)
            |otherwise = Left ((Node  (fmap unNodeEntry es1),  p1 )
                              ,(Node (fmap unNodeEntry es2), p2 ))
                -- The new entries after insert
        where   newEs = case insertSubtree of
                          Right newSub -> S.adjust (const newSub) minIdx es
                          Left split -> notMinTree <> S.fromList [fst split,snd split]
                -- The optimal subtree to insert into
                (minSubtree ,~(notMinTree,minIdx))= chooseSubtree es (toIns,pred)
                -- The changed (and additional) subtree after insert
                insertSubtree = insertAndSplit minSubtree (min,max) (toIns,pred)
                -- The split of the node entries (in case of overpopulation)
                ~(~(p1,es1),~(p2,es2)) =  pickSplit $ fmap NodeEntry newEs

insertAndSplit (Leaf es,p) (min,max) (toIns,pred)
            |length newEs <= max  = Right (Leaf newEs,union $ fmap (Right .snd) newEs)
            |otherwise = Left ((Leaf (fmap unLeafEntry es1), union $ fmap entryPredicate es1)
                        ,(Leaf (fmap unLeafEntry es2), union $ fmap entryPredicate es2))
            -- The optimal subtree to insert into
    where   newEs = ((toIns,pred) :< es)
            -- The split of the node entries (in case of overpopulation)
            ~(~(p1,es1),~(p2,es2)) =  pickSplit $ fmap LeafEntry newEs


-- A helper function that propagates deletion through the subtrees and condenses.
-- If an internal node is underpopulated after deletion, the node and all it's subnodes are removed
-- and all their leaf entries are stored for reinsertion. The deletion is then propagated to the parent
-- of the node
deleteAndCondense :: Predicates p  => NodeEntry GiST p a -> (Int,Int) -> p  -> (NodeEntry GiST p a, Seq (LeafEntry p a))
deleteAndCondense (Node es, pred) (min, max) p
        |length newEs < min = ((Null, union (S.singleton (Right p))), toAdd <> S.filter (not . consistent (Right p) .Right .snd ) (getEntriesS (Node es)))
        |otherwise          = ((Node newEs, union $ fmap treePred  newEs), toAdd)
            -- The new entries after delete without Null entries
    where   newEs = S.filter (not.isNull) (fmap fst delNodes)
            -- The propagated entries to add
            toAdd = join (fmap snd delNodes)
            -- The entries after delete
            delNodes =  fmap (\e -> if (consistent (Right p) (Left $ snd e))
                            then (deleteAndCondense e (min,max) p)
                            else (e,Empty)) es
-- If a leaf is underpopulated after deletion, the leaf is removed and all its entries are
-- stored for reinsertion. The deletion is then propagated to the parent of the node
deleteAndCondense ((Leaf es),pred) (min, max) p
    |length newEs < min = ((Null,pred), newEs)
    |otherwise          = ((Leaf newEs, union $ fmap (Right .snd) newEs),Empty)
                -- The new entries after delete without Null entries
          where   newEs = S.filter (not . consistent (Right p) .Right .snd) es



-- Inserts multiple entries into a GiST
insertMultiple :: (Predicates p ) => Seq (LeafEntry p a) -> GiST p a -> (Int,Int) -> GiST p a
insertMultiple Empty gist _ = gist
insertMultiple (e:<es) gist (min,max) = insertMultiple es afterInsert (min,max)
    where afterInsert = insert e (min,max) gist



-- Chooses the most appropriate subtree to insert the entry into
chooseSubtree   :: Predicates p  =>Seq (NodeEntry GiST p a) -> LeafEntry p a -> (NodeEntry GiST p a,(Seq (NodeEntry GiST p a),Int))
chooseSubtree subtrees e  = fst  $ minimumBy (comparing (\(~(_,p))-> p)) $ penalties
  where   penalties = S.mapWithIndex (\k ne -> ((ne,(deleteAt k subtrees,k)), penalty (Right $ snd e) (Left $ snd ne)) ) subtrees


-- Takes an entry and extracts the GiST from it
makeRoot :: NodeEntry GiST p a -> GiST p a
makeRoot (Node es, p) = Node es
makeRoot (Leaf es, p) = Leaf es


-- Checks if an entry contains a Null GiST
isNull :: NodeEntry GiST p a -> Bool
isNull (Null, p) = True
isNull _ = False


-- Returns all the entries stored in a GiST
getEntries :: GiST p a -> [LeafEntry p a]
getEntries (Node es) = concat [getEntries sub | (sub,_) <- F.toList es]
getEntries (Leaf es) = F.toList es

getEntriesS :: GiST p a -> Seq (LeafEntry p a)
getEntriesS (Node es) = join $ fmap (\(sub,_) -> getEntriesS sub ) es
getEntriesS (Leaf es) = es



-- | Returns all the data stored in a GiST
getData :: GiST p a -> [a]
getData gist = fmap fst $ getEntries gist

-- | Return the number of values in a GiST
size :: GiST p a -> Int
size gist = length $ getEntries gist



