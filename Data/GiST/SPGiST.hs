{-# LANGUAGE StandaloneDeriving,TupleSections,PatternSynonyms,ViewPatterns,FlexibleInstances,DeriveTraversable , DeriveFoldable,DeriveFunctor,DeriveGeneric,TypeFamilies ,FlexibleContexts,ScopedTypeVariables #-}
module Data.GiST.SPGiST where

import Data.Tuple
import Data.Either (isRight,isLeft)
import Data.Monoid
import Data.Ord
import Control.Monad
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


class (Show p , Show (Node p) ,Eq p )=> Predicates p where

    -- Node API
    data Node p


    -- Node origin value
    origin :: Node p

    -- lift node to predicate
    leaf :: Node p -> p

    -- append two prefixes
    append :: Node p -> Node p -> Node p

    -- add nodes node
    neg :: p -> p
    neg i = i

    delta :: Node p -> Node p -> p
    delta  _  _ = leaf origin
    deltaMinus :: Node p -> Node p -> p
    deltaMinus  _  _ = leaf origin
    applyN :: p ->  Node p  ->  Node p
    applyN _ j  = j

    applyL :: p ->  p  ->  p
    applyL _ i = i

    add :: Node p -> Node p -> Node p
    add = flip const
    remove :: Node p  -> Node p -> Node p
    remove = flip const

    -- lift predicate to node
    bound :: p -> Node p

    -- Split predicate with node
    splitPrefix :: p -> Node p -> Either (Node p,(Maybe (Node p ) , Maybe (Node p))) p


    -- | Checks if the given entry is consistent with a given predicate
    -- Make the leaf a new predicate
    -- Create A new Origin predicate from leaf
    consistent  :: Either (Node p) p -> Either (Node p) p -> Bool

    type Query p
    -- | Check if the given query is consistent with a given predicate
    match :: Query p -> Either (Node p) p -> Bool

    -- | Returns a predicate that is the union of all predicates of the given list of entries
    -- | Calculates a numerical penalty for inserting the entry containing the first predicate
    -- into a subtree rooted at an entry containing the second predicate
    -- | Given a list of entries, returns two disjunct subsets that contain the entries in the list.
    -- Focus is on minimising the overlap between the splitted entries' predicates
    pickSplitN :: Seq (Entry f p b) -> (Node p ,Maybe b ,Seq (Node p,Maybe b,Seq (Entry f p b)))

    chooseSubTree :: p ->  b -> GiST p b -> Either (GiST p b) Int


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

search  :: (Predicates p ) => p -> GiST p a -> [a]
search i = F.toList . searchKey i

searchKey  :: (Predicates p ) => p -> GiST p a -> Seq a
-- searchKey  i j | traceShow (i,j) False = undefined
searchKey  p (Leaf pre m es)
  | isLeft psm = maybe S.empty S.singleton m
  | otherwise =  fmap fst $ S.filter (consistent (Right ps) . Right . snd ) es
  where
    psm@(~(Right ps)) = traceShowId $ splitPrefix p pre
searchKey  p (Node pre  m  es)
  | isLeft psm = maybe S.empty S.singleton m
  | otherwise =  join $ fmap (\e -> if consistent (Right ps) (Left $ prefix e)
           then searchKey ps e
           else S.empty ) es
  where
    psm@(~(Right ps)) = traceShowId $ splitPrefix p pre
searchKey _ (Node _ _ Empty) = S.empty



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
  | isLeft psm  = Node pre Nothing n
  | otherwise = collapse
  where
    psm@(~(Right ps)) = splitPrefix pr pre
    matched = (\po -> if consistent (Right ps ) (treePred po) then Right po else Left po ) <$> n
    newMatched = either id (flip delete ps) <$> matched
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
  | isLeft psm = if S.null  n then empty else Leaf pre Nothing n
  | otherwise =newPrefix
  where
    psm@(~(Right ps)) = splitPrefix  p pre
    matched = (\po -> if consistent (Right ps ) (Right $ snd po) then Nothing else Just po ) <$> n
    allCons = all isNothing matched
    newMatched = edit (applyL dt) . fromJust <$>  (maybe id (\d -> (Just (d,leaf origin):<)) m) (S.filter isJust matched)
    edit f (j,i) =(j,f i)
    dt = deltaMinus (bound p) pre
    newPrefix = if L.null newMatched && isNothing m -- check newPrefix for emptyness
                   then empty -- set leaf to emtpy
                   else Leaf (remove (bound p) pre) (fmap fst $ L.find ((==leaf origin) . snd ) newMatched) (S.filter ((/= leaf origin).snd) newMatched)


fromLeft (Left i) = i
fromRight (Right i)  = i




insertSplit :: (Show a ,Predicates p) => SPGistConfig  -> GiST p a -> p -> a -> GiST p a
insertSplit c no@(Node prefix m n ) pr v
  = case splitPrefix pr prefix of
      Left (ssp,(npr,nprefix)) ->  if isNothing npr
                       then if isJust nprefix then Node (add (bound pr ) ssp ) (Just v) (pure no) else Node  prefix (Just v) n
                       else Node (add (bound pr ) ssp )Nothing (S.fromList [Node (add (bound pr ) $ fromJust nprefix) m n,Leaf origin Nothing (pure (v,leaf $ fromJust npr))])
      Right token ->
           let
            newMatched = S.adjust (\n -> insertSplit c n token v ) (fromRight matched) n
            ns = search dt <$> n
            matched = chooseSubTree pr v no
            anyCons = isRight matched
            newPrefix = if anyCons  then (Node (add (bound pr )prefix )m ( fmap (edit (applyN dt)) newMatched )) else (Node (add (bound pr ) prefix) m $ fmap (edit (applyN dt)) (n :> fromLeft matched))
            edit f (Leaf p i v ) = (Leaf (f p ) i v)
            edit f (Node p i v ) = (Node (f p ) i v)
            dt = delta (bound pr) (prefix)
          in  traceShow ns newPrefix

insertSplit c (Leaf pre da l) p v
  = case splitPrefix p pre of
      Left  (ssp ,(npr,nprefix)) -> if isNothing npr
              then Leaf pre (Just v) l
              else Node ssp Nothing (S.fromList [Leaf (fromJust nprefix) da l,Leaf origin Nothing (pure (v,leaf $ fromJust npr))])
      Right token ->
        let
          (prefix,vn,n) = pickSplitN (maybe id (\i -> (:> (LeafEntry (i,leaf origin)))) da $ fmap LeafEntry ((v,token) :<  l))
          newNodes = if anyCons then (either id id <$> cons) else fmap (edit (applyL dt)) ( maybe id (\d -> ((d,leaf origin):<)) da $  (v,token) :<  l)
          cons = (\po -> if consistent (Right token ) (Right $ snd po) then (Right (v,snd po)) else (Left po) )  <$> l
          anyCons = any isRight cons
          edit f (j,i) =(j,f i)
          dt = delta (bound p) pre

       in if spacePartitions  c < length newNodes
           then Node (append pre prefix) vn (fmap (\(p,v,s) -> Leaf p v (fmap unLeafEntry s) ) n)
           else Leaf (if anyCons then pre else add (bound p) pre) (fmap fst $ L.find ((==leaf origin) . snd ) newNodes) (S.filter ((/= leaf origin).snd) newNodes)

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

instance (Predicates p ,Show (Node p),Show a ,Show p) => Show (GiST p a ) where
  show (Node p v l ) = "N" ++ show (p )++ " -> "  ++  maybe "" (\i -> "="++ show i  ) v ++ " [" ++ intercalate "," ( F.toList  $ fmap (\(g) ->   show g ) l) ++ "]"
  show (Leaf p v l ) =  "L" ++ show (p) ++ " -> "  ++  maybe "" (\i -> "="++ show  i ) v ++ " [" ++ intercalate "," (  F.toList  $fmap (\(g,p) ->   show p  ++ " = "  ++ show g) l) ++ "]"

first f (i,j) = (f i,j)
groupBy                 :: (a -> a -> Bool) -> Seq a -> Seq (Seq a)
groupBy _  Empty           =  Empty
groupBy eq (x:<xs)       =  (x:<ys) :< groupBy eq zs
                           where (ys,zs) = S.spanl (eq x) xs

conf = (SPGistConfig NeverShrink 4 4)

opbi f l  i j = f (l i ) (l j)
