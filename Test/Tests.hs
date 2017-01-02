{-# LANGUAGE FlexibleContexts,MultiParamTypeClasses
    #-}

module Test where

import Data.GiST.GiST
import Data.List(sort)
import qualified Data.Foldable as F
import qualified Data.GiST.BTree as BTree
-- import qualified Data.GiST.RTree as RTree
-- | A small series of tests on the functionality of the GiST

bounds = (2,5)
-- empty GiST

bg1 = empty::GiST Int Int
-- some elements added
bg2 = insert (50,  50) bounds $ insert (32,  32) bounds $ insert (7,  7) bounds $  insert (16,  16) bounds $ insert (85,  85) bounds $ insert (63,  63) bounds $ insert (42,  42) bounds $ insert (98,  98) bounds $ insert (25,  25) bounds $ insert (73,  73) bounds $ insert (36,  36) bounds $ insert (1,  1) bounds $ insert (62,  62) bounds bg1
-- search test
bs1 = search ( 32) bg2
-- bt1 = (sort bs1) == [36, 42, 50]
-- search test 2
bs2 = query (BTree.Contains (43,82)) bg2
--bt2 = (sort bs2) == [50, 62, 63, 73]
-- some elements deleted
bg3 = delete ( 25) bounds $ delete ( 73) bounds $ delete ( 1) bounds bg2
-- search test 3
bs3 = query (BTree.Contains (20,45)) bg3
--bt3 = sort bs3 == [32, 36, 42]
-- test results
--b = [bt1,bt2,bt3]
  {-
--empty gist
rg1 = empty:: GiST (RTree.Predicate (Int,Int)) (Int,Int)
-- some elements added
rg2 = insert ((50,23), RTree.Equals (50,23)) bounds $ insert ((32,63), RTree.Equals (32,63)) bounds $ insert ((35,7), RTree.Equals (35,7)) bounds $  insert ((23,16), RTree.Equals (23,16)) bounds $ insert ((2,85), RTree.Equals (2,85)) bounds $ insert ((63,63), RTree.Equals (63,63)) bounds $ insert ((72,42), RTree.Equals (72,42)) bounds $ insert ((33,98), RTree.Equals (33,98)) bounds $ insert ((12,25), RTree.Equals (12,25)) bounds $ insert ((73,54), RTree.Equals (73,54)) bounds $ insert ((45,36), RTree.Equals (45,36)) bounds $ insert ((27,41), RTree.Equals (27,41)) bounds $ insert ((53,62), RTree.Equals (53,62)) bounds rg1
-- search test 1
rs1 = search (RTree.Contains ((12,64),(34,33))) rg2
rt1 = (sort rs1) == [(27,41), (32,63)]
-- search test 2
rs2 = search (RTree.Contains ((43,75),(82,33))) rg2
rt2 = (sort rs2) == [(45,36),(53,62),(63,63), (72,42),(73,54)]
-- some elements deleted
rg3 = delete (RTree.Equals (12,25)) bounds $ delete (RTree.Equals (73,54)) bounds $ delete (RTree.Equals (27,41)) bounds rg2
-- search test 3
rs3 = search (RTree.Contains ((20,50),(45,35))) rg3
rt3 = sort rs3 == [(45,36)]
--test results
r = [rt1,rt2,rt3]


-}
main = do
  print (F.toList $ testInsDel [0 :: Int ..100])
  print (testInsUpdate [0 :: Int ..100])

testIns s =
   foldl (\ m  i-> insert (i,  i) (3,6) m) empty ( s)
testDel s  m =
   foldl (\ m  i-> delete ( i) (3,6) m) m ( s)

testUpdate f s  m =
  foldl (\ m  i-> update ( i) f  m) m ( s)

testInsDel l = testDel l $ testIns l
testInsUpdate l = F.toList (testUpdate (+ (-1)) l $testUpdate (+1) l $ testIns l) == F.toList (testIns l)


