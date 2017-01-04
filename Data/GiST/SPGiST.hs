{-# LANGUAGE StandaloneDeriving,TupleSections,PatternSynonyms,ViewPatterns,FlexibleInstances,DeriveTraversable , DeriveFoldable,DeriveFunctor,DeriveGeneric,TypeFamilies ,FlexibleContexts,ScopedTypeVariables #-}
module Data.GiST.SPGiST where

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

data Policy
  = NeverShrink
  | LeafShrink
  | PathShrink

data SPGistConfig
  = SPGistConfig
  { shrinkPolicy :: Policy
  , spaceResolution :: Int
  , spacePartitions :: Int
  }



pattern Empty   <- (S.viewl -> S.EmptyL)  where Empty = S.empty
pattern x :< xs <- (S.viewl -> x S.:< xs) where (:<)  = (S.<|)
pattern xs :> x <- (S.viewr -> xs S.:> x) where (:>)  = (S.|>)


class Predicates p where
    -- Node API
    data Node p
    -- Node origin value
    origin :: Node p
    -- lift node to predicate
    leaf :: Node p -> p
    node ::  p -> Node p
    -- Split node predicate
    split :: p -> Node p -> Maybe p
    splitPre :: p -> Node p -> (Node p,(Maybe (Node p ) , Maybe (Node p)))
    append :: Node p -> Node p -> Node p

    type Query p
    -- | Checks if the given entry is consistent with a given predicate
    -- Make the leaf a new predicate
    -- Create A new Origin predicate from leaf
    consistent  :: Either (Node p) p -> Either (Node p ) p -> Bool
    -- | Check if the given query is consistent with a given predicate
    match :: Query p -> Either (Node p) p -> Bool
    -- | Returns a predicate that is the union of all predicates of the given list of entries
    merge :: Either (Node p) p -> Either (Node p) p -> Node p

    -- | Calculates a numerical penalty for inserting the entry containing the first predicate
    -- into a subtree rooted at an entry containing the second predicate
    -- | Given a list of entries, returns two disjunct subsets that contain the entries in the list.
    -- Focus is on minimising the overlap between the splitted entries' predicates
    pickSplitN :: Seq (Entry f p b) -> (Node p ,Maybe b ,Seq (Node p,Maybe b,Seq (Entry f p b)))
    chooseTree :: p -> GiST p b -> Maybe Int


-- | A general entry type for the gist
data Entry f p a = LeafEntry !(LeafEntry p a)
                 | NodeEntry !(NodeEntry f p a)


unLeafEntry  (LeafEntry l) =  l
{-# INLINE unLeafEntry #-}
unNodeEntry  (NodeEntry n) =  n
{-# INLINE unNodeEntry #-}

-- | Returns the predicate of this entry
entryPredicate :: Entry f p a -> Either (Node p) p
entryPredicate (LeafEntry e) = Right $ snd e
entryPredicate (NodeEntry e) = Left $ snd e
{-# INLINE entryPredicate #-}

-- | A leaf entry has a predicate and data
type LeafEntry p a = (a,p )

-- | A node entry has a predicate and a subtree
type NodeEntry f p a = (f p a, Node p )


type PrefixEntry f p a =  (f p a, p)
-- | The data structure used for building the GiST
data GiST p a  = Leaf !(Node p) !(Maybe a) !(Seq (LeafEntry p a))       -- ^ leaf node
               | Node !(Node p) !(Maybe a) !(Seq (GiST p a))
               deriving (Functor,F.Foldable,T.Traversable,Generic)

deriving instance (Eq p , Eq (Node p) , Eq a) => Eq (GiST p a)

prefix :: GiST p a -> Node p
prefix (Leaf p _ _ ) = p
prefix (Node p _ _ ) = p

searchKey  :: (Show p , Show a ,Predicates p ) => p -> GiST p a -> [a]
-- searchKey  i j | traceShow (i,j) False = undefined
searchKey  p (Leaf pre m es)
  | isNothing psm = maybeToList m
  | otherwise =  fmap fst $ F.toList $ S.filter (consistent (Right ps) . Right . snd ) es
  where
    psm@(Just ps) = split p pre
searchKey  p (Node pre  m  es)
  | isNothing psm = maybeToList m
  | otherwise =  concat $ F.toList $ fmap (\e -> if consistent (Right ps) (Left $ prefix e)
           then searchKey ps e
           else [] ) es
  where
    psm@(Just ps) = split p pre
searchKey _ (Node _ _ Empty) = []



-- deleteNeverShrink :: (Show (Node p),Show a,Show p,Predicates p) => SPGistConfig -> GiST p a -> S.Seq p -> Int -> GiST p a

isNull (Leaf _ i  j ) = S.null j
isNull (Node _ _  j )  = S.null j

nodeData  (Leaf _ i j ) = i
nodeData (Node _ i j ) = i

empty :: Predicates p => GiST p a
empty = Leaf origin Nothing S.empty

isEmpty (Leaf _ i j ) = isNothing i
isEmpty (Node _ i j ) = isNothing i

nodePred :: GiST p a -> Either (Node p) p
nodePred (Node p _  _ )  = Left  p

treePred :: GiST p a -> Either (Node p) p
treePred p   = Left (prefix p)

filterJust = fmap fromJust . S.filter isJust

delete :: Predicates p =>  GiST p a -> p -> GiST p a
-- delete n p | traceShow  (n,p) False = undefined
delete (Node pre m n) pr
  | isNothing psm  = Node pre Nothing n
  | otherwise = collapse
  where
    psm@(~(Just ps)) = split pr pre
    matched = (\po -> if consistent (Right ps ) (treePred po) then Right po else Left po ) <$> n
    newMatched = either id (\i -> delete i ps  ) <$> matched
    nonEmpty = S.filter (\i -> not (isNull (i))) newMatched
    notEmptyNull = S.filter (\i -> not (isEmpty i) || not (isNull (i))) newMatched
    toLeaf = (filterJust $ (\n -> (,leaf $ prefix n) <$> nodeData n)<$> newMatched)
    merge (Leaf lp lv v)
      | isNothing lv || isNothing m = Leaf (pre `append` lp ) (lv <|> m) v
      | otherwise = Node pre m nonEmpty
    merge (Node lp lv v)
      | isNothing lv || isNothing m = Node (pre `append` lp ) (lv <|> m) v
      | otherwise = Node pre m nonEmpty
    collapse = if all (\i -> (not. isEmpty) (i) && isNull (i)) nonEmpty
                  then if L.null toLeaf  -- check if leafs are empty
                          then empty -- set node to empty
                          else Leaf pre m toLeaf
                  else if F.length notEmptyNull == 1
                        then merge (S.index notEmptyNull 0)
                        else Node pre m  notEmptyNull
delete (Leaf pre m n) p
  | isNothing psm = Leaf pre Nothing n
  | otherwise =newPrefix
  where
    psm@(~(Just ps)) = split  p pre
    matched = (\po -> if consistent (Right ps ) (Right $ snd po) then Nothing else Just po ) <$> n
    allCons = all isNothing matched
    newMatched = fmap fromJust $ S.filter isJust matched
    newPrefix = if L.null newMatched && isNothing m -- check newPrefix for emptyness
                   then empty -- set leaf to emtpy
                   else Leaf pre m newMatched




insertSplit :: Predicates p => SPGistConfig  -> GiST p a -> p -> a -> GiST p a
insertSplit c no@(Node prefix m n ) pr v
  | isNothing psm = if isNothing npr
                       then Node ssp (Just v) (pure no)
                       else Node ssp Nothing (S.fromList [Node (fromJust nprefix) m n,Leaf origin Nothing (pure (v,leaf $ fromJust npr))])
  | otherwise = newPrefix
  where
    psm@(~(Just token ))= split pr prefix
    (ssp ,(npr,nprefix)) = splitPre pr prefix
    new =  insertSplit c empty token v
    newMatched = S.adjust (\n -> insertSplit c n token v ) (fromJust matched) n
    matched = chooseTree pr no
    anyCons = isJust matched
    newPrefix = if anyCons  then (Node prefix m newMatched ) else (Node prefix m $n :> new)

insertSplit c (Leaf pre da l) p v
  | isNothing psm = if isNothing npr
                       then Leaf pre (Just v) l
                       else Node ssp Nothing (S.fromList [Leaf (fromJust nprefix) da l,Leaf origin Nothing (pure (v,leaf $ fromJust npr))])
  | spacePartitions  c < length newNodes  && anyCons = Node prefix vn (fmap (\(p,v,s) -> Leaf p v (fmap unLeafEntry s) ) n)
  | otherwise = Leaf pre da newNodes
 where (prefix,vn,n) = pickSplitN (fmap LeafEntry newNodes)
       (ssp ,(npr,nprefix)) = splitPre p pre
       newNodes = if anyCons then (either id id <$> cons) else (v,token) :< l
       cons = (\po -> if consistent (Right token ) (Right $ snd po) then (Right po ) else (Left po) )  <$> l
       anyCons = any isRight cons
       psm@(~(Just  token ))= split p pre


{-
makeLeaf n (token :- NEmpty )  =  Leaf token (Just n) S.empty
makeLeaf n (token :- ps)  =  Leaf token Nothing (pure (n,ps))

insertNeverShrink :: Predicates p => SPGistConfig -> GiST p a -> p -> a -> GiST p a

insertNeverShrink conf (Node pre m n) NEmpty v= Node pre (Just v) n
insertNeverShrink conf (Node pre m n) p@( token :- ps) v
  | otherwise = newPrefix
  where
    matched = (\po -> if consistent (Left token) (treePred po) then Right po  else Left po ) <$> n
    anyCons = any isRight matched
    new =  insertNeverShrink  conf (Leaf (token ) Nothing  S.empty ) ps v
    newMatched = either id (\n-> insertNeverShrink conf n ps v ) <$> matched
    newPrefix = if anyCons  then (Node pre m newMatched ) else (Node pre m $n :> (new))

insertNeverShrink conf (Leaf pre m n ) p@( token :- NEmpty ) v
  = (Leaf pre m (n :> (v,p)))
insertNeverShrink conf (Leaf pre m n ) p@( token :- ps) v
  | otherwise = newPrefix
  where
    matched = (\po -> if consistent (Left token) (Right $ snd po) then Right po  else Left po ) <$> n
    anyCons = any isRight matched
    new =  insertNeverShrink  conf (Leaf token Nothing Empty ) (ps) v
    newMatched = either (\(n,t) -> makeLeaf  n t  ) (\(n,t)-> (insertNeverShrink conf (makeLeaf n t ) (ps) v )) <$> matched
    newPrefix = if anyCons  then (Node pre Nothing newMatched ) else (Node pre Nothing $newMatched :> new)
-}

instance (Show (Node p),Show a ,Show p) => Show (GiST p a ) where
  show (Node p v l ) = "N" ++ show p ++ " -> "  ++  maybe "" (\i -> "="++ show i  ) v ++ " [" ++ intercalate "," ( F.toList  $ fmap (\(g) ->   show g ) l) ++ "]"
  show (Leaf p v l ) =  "L" ++ show p ++ " -> "  ++  maybe "" (\i -> "="++ show  i ) v ++ " [" ++ intercalate "," (  F.toList  $fmap (\(g,p) ->   show p  ++ " = "  ++ show g) l) ++ "]"

first f (i,j) = (f i,j)
groupBy                 :: (a -> a -> Bool) -> Seq a -> Seq (Seq a)
groupBy _  Empty           =  Empty
groupBy eq (x:<xs)       =  (x:<ys) :< groupBy eq zs
                           where (ys,zs) = S.spanl (eq x) xs

conf = (SPGistConfig NeverShrink 20 4)

opbi f l  i j = f (l i ) (l j)
