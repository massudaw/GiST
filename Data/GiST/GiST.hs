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
    ,FlexibleContexts
    #-}

module Data.GiST.GiST
    (
        -- ** Types
        GiST
        ,Entry(..)
        ,Predicates(..)
        ,LeafEntry,NodeEntry
        ,entryPredicate
        ,getEntries
        -- ** GiST operations
        ,search, insert, delete, empty, save, load, getData, size
    ) where

import Data.GiST.Types
import qualified Data.Text.IO as TIO
import qualified Data.Text as T
import Data.List (null,minimumBy)
import Data.Ord (comparing)


-- | Searches the GiST for leaf nodes that satisfy the given search predicate
search  :: Predicates p  => p  -> GiST p a -> [a]
search  p (Leaf es)     = [fst e | e <- es, consistent p (snd e)]
search  _ (Node [])     = []
search  p (Node (e:es))
    |consistent p (snd e) = (search p (fst e)) ++ (search p (Node es))
    |otherwise                  = search p (Node es)

-- | Inserts an entry into the tree, rebalancing the tree if necessary.
-- Rebalancing is done to satisfy the minimum and maximum fill factor
-- of the tree (represented as an integer tuple)
insert  :: Predicates p  => LeafEntry p a -> (Int, Int) -> GiST p a -> GiST p a
insert (toIns, pred) (min,max) (Node es)
        |not $ null $ search pred (Node es) = Node es
        |length newEs <= max   =  Node newEs
        |otherwise              = Node [(Node $ map unNodeEntry es1, union $ map entryPredicate es1)
                                    ,(Node $ map unNodeEntry es2, union $ map entryPredicate es2)]
            -- The new entries after inserting
    where   newEs = case insertSubtree of
                        Right newSub -> [if (snd e == snd minSubtree)
                                            then newSub
                                            else e
                                        |e <- es]
                        Left split -> (filter ((/=snd minSubtree).snd) es)++[fst split,snd split]
            -- The optimal subtree to insert into
            minSubtree = chooseSubtree es (toIns,pred)
            -- The changed (and additional) subtree after insert
            insertSubtree = insertAndSplit minSubtree (min,max) (toIns,pred)
            -- The split of the node entries (in case of overpopulation)
            (es1,es2) =  pickSplit $ map NodeEntry newEs

insert (toIns, p) (min,max) (Leaf es)
        |not $ null $ search p (Leaf es) = Leaf es
        |length newEs <= max    = Leaf newEs
        |otherwise              = Node [(Leaf $ map unLeafEntry es1,union $ map entryPredicate es1)
                                    ,(Leaf $ map unLeafEntry es2, union $ map entryPredicate es2)]
            -- The new entries after insert
    where   newEs = (toIns, p):es
            -- The split of the node entries (in case of overpopulation)
            (es1,es2) =  pickSplit $ map LeafEntry newEs

-- | Deletes a leaf entry from the tree, rebalancing the tree if necessary.
-- Rebalancing is done to satisfy the minimum and maximum fill factor
-- of the tree (represented as an integer tuple)
delete  :: Predicates p  => p  -> (Int, Int) -> GiST p a -> GiST p a
delete p (min,max) (Node es)
        |length newEs == 1  = insertMultiple toAdd (makeRoot $ head newEs) (min,max)
        |otherwise          = insertMultiple toAdd (Node newEs) (min, max)
            -- The new entries after delete without Null entries
    where   newEs = filter (not.isNull) (map fst delNodes)
            -- The propagated entries to add
            toAdd = concat (map snd delNodes)
            -- The entries after delete
            delNodes =  [if (consistent p (snd e))
                            then (deleteAndCondense e (min,max) p)
                            else (e,[])
                        |e <- es]

delete p (min,max) (Leaf es) = Leaf [e | e <- es, not $ consistent p (snd e)]

-- | Create a new empty GiST
empty :: GiST p a
empty = Leaf []

-- | Loads a GiST from file
load :: (Read a, Read p ) => FilePath -> IO (GiST p a)
load f = do s <- TIO.readFile f
            return (read $ T.unpack s)

-- | Saves the GiST to file
save :: (Show a, Show p ) => GiST p a -> FilePath -> IO ()
save gist f = TIO.writeFile f $ T.pack (show gist)




-- | A helper function that propagates insertion through the subtrees and splits when necessary.
-- If the node is overpopulated after the insertion, the node is split into
-- two smaller nodes which are then added to the parent
insertAndSplit :: Predicates p  => NodeEntry p a -> (Int,Int) -> LeafEntry p a -> Either (NodeEntry p a, NodeEntry p a) (NodeEntry p a)
insertAndSplit (Node es,p) (min,max) (toIns,pred)
            |length newEs <= max  =  Right (Node newEs,union $ map snd newEs)
            |otherwise = Left ((Node  (map unNodeEntry es1), union $ map entryPredicate es1)
                        ,(Node (map unNodeEntry es2), union $ map entryPredicate es2))
                -- The new entries after insert
        where   newEs = case insertSubtree of
                            Right newSub -> [if (snd e == snd minSubtree)
                                                then newSub
                                                else e
                                            |e <- es]
                            Left split -> (filter ((/= snd minSubtree). snd) es)++[fst split,snd split]
                -- The optimal subtree to insert into
                minSubtree = chooseSubtree es (toIns,pred)
                -- The changed (and additional) subtree after insert
                insertSubtree = insertAndSplit minSubtree (min,max) (toIns,pred)
                -- The split of the node entries (in case of overpopulation)
                (es1,es2) =  pickSplit $ map NodeEntry newEs

insertAndSplit (Leaf es,p) (min,max) (toIns,pred)
            |length newEs <= max  = Right (Leaf newEs,union $ map snd newEs)
            |otherwise = Left ((Leaf (map unLeafEntry es1), union $ map entryPredicate es1)
                        ,(Leaf (map unLeafEntry es2), union $ map entryPredicate es2))
            -- The optimal subtree to insert into
    where   newEs = ((toIns,pred) : es)
            -- The split of the node entries (in case of overpopulation)
            (es1,es2) =  pickSplit $ map LeafEntry newEs


-- A helper function that propagates deletion through the subtrees and condenses.
-- If an internal node is underpopulated after deletion, the node and all it's subnodes are removed
-- and all their leaf entries are stored for reinsertion. The deletion is then propagated to the parent
-- of the node
deleteAndCondense :: Predicates p  => NodeEntry p a -> (Int,Int) -> p  -> (NodeEntry p a, [LeafEntry p a])
deleteAndCondense (Node es, pred) (min, max) p
        |length newEs < min = ((Null, p), toAdd ++ filter (not . consistent p . snd) (getEntries (Node es)))
        |otherwise          = ((Node newEs, union $ map snd newEs), toAdd)
            -- The new entries after delete without Null entries
    where   newEs = filter (not.isNull) (map fst delNodes)
            -- The propagated entries to add
            toAdd = concat (map snd delNodes)
            -- The entries after delete
            delNodes =  [if (consistent p (snd e))
                            then (deleteAndCondense e (min,max) p)
                            else (e,[])
                        |e <- es]
-- If a leaf is underpopulated after deletion, the leaf is removed and all its entries are
-- stored for reinsertion. The deletion is then propagated to the parent of the node
deleteAndCondense ((Leaf es),pred) (min, max) p
    |length newEs < min = ((Null,pred), newEs)
    |otherwise          = ((Leaf newEs, union $ map snd newEs),[])
                -- The new entries after delete without Null entries
        where   newEs = [e | e <- es, not $ consistent p (snd e)]



-- Inserts multiple entries into a GiST
insertMultiple :: (Predicates p ) => [LeafEntry p a] -> GiST p a -> (Int,Int) -> GiST p a
insertMultiple [] gist _ = gist
insertMultiple (e:es) gist (min,max) = insertMultiple es afterInsert (min,max)
    where afterInsert = insert e (min,max) gist



-- Chooses the most appropriate subtree to insert the entry into
chooseSubtree   :: Predicates p  =>[(NodeEntry p a)] -> LeafEntry p a -> (NodeEntry p a)
chooseSubtree subtrees e    = fst  $ minimumBy (comparing snd) $ penalties
        where   penalties = [(ne, penalty (snd e) (snd ne))|ne <- subtrees]


-- Takes an entry and extracts the GiST from it
makeRoot :: NodeEntry p a -> GiST p a
makeRoot (Node es, p) = Node es
makeRoot (Leaf es, p) = Leaf es


-- Checks if an entry contains a Null GiST
isNull :: NodeEntry p a -> Bool
isNull (Null, p) = True
isNull _ = False


-- Returns all the entries stored in a GiST
getEntries :: GiST p a -> [LeafEntry p a]
getEntries (Node es) = concat [getEntries sub | (sub,_) <- es]
getEntries (Leaf es) = es


-- | Returns all the data stored in a GiST
getData :: GiST p a -> [a]
getData gist = map fst $ getEntries gist

-- | Return the number of values in a GiST
size :: GiST p a -> Int
size gist = length $ getEntries gist
