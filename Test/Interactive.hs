{-# LANGUAGE MultiParamTypeClasses
    #-}

module Main where

import System.IO
import System.Exit
import Data.GiST.GiST
import qualified Data.GiST.BTree as BTree
import qualified Data.GiST.RTree as RTree
import Control.Monad(when)
import System.Environment(getArgs)
import System.Console.GetOpt
import qualified Data.Text.IO as TIO
import qualified Data.Text as T

-- | A small programm used for adding, deleting or searching data in a GiST saved on a file
-- options b and r choose between a BTree or RTree implementation
-- Option e for creating an empty gist, i for adding data into the tree, d for deleting and s for searching
main    :: IO()
main =  do
    args <- getArgs  
    let (flags, nonOpt, msgs) = getOpt RequireOrder options args
    when (length flags /=2) $ do 
        putStrLn "usage : main <-b|-r> <-i key|-d key|-s interval|-e> file" 
        exitFailure
    when (length nonOpt /= 1) $ do
        putStrLn "usage : main <-b|-r> <-i key|-d key|-s interval|-e> file"
        exitFailure
    let treeFlag = head flags
    let opFlag = flags!!1
    let file = nonOpt!!0
    if (treeFlag == BTree ) then do
        if (opFlag == Empty) then save (empty::GiST BTree.Predicate Int) file
        else do
            gist <- load file
            executeOperationB gist opFlag file
    else do
        if (opFlag == Empty) then save (empty::GiST RTree.Predicate (Int,Int)) file
        else do
            gist <- load file
            executeOperationR gist opFlag file
    
    
    
data Flag = BTree | RTree | Search String | Insert String | Delete String | Empty deriving (Eq)

options :: [OptDescr Flag]
options = [
    Option ['b'] ["btree"] (NoArg BTree)  "use BTree GiST",
    Option ['r'] ["rtree"] (NoArg RTree)  "use RTree GiST",
    Option ['s'] ["search"] (ReqArg Search  "DATA")  "search in GiST",
    Option ['i'] ["insert"] (ReqArg Insert  "DATA") "insert into GiST",
    Option ['d'] ["delete"] (ReqArg Delete  "DATA") "delete from GiST",
    Option ['e'] ["empty"] (NoArg Empty) "write empty GiST"
  ]
   
executeOperationB :: GiST BTree.Predicate Int -> Flag -> String -> IO()
executeOperationB gist (Insert s) file  = do     
    let key = read s :: Int
    save (insert (key, BTree.Equals key) (2,4) gist) file
executeOperationB gist (Delete s) file = do
    let key = read s :: Int 
    save (delete (key, BTree.Equals key) (2,4) gist) file 
executeOperationB gist (Search s) file = do
    let (min,max) = read s :: (Int,Int)
    when (min >= max) $ do
        putStrLn "usage for BTree : main <-i key|-d key|-s (min,max)>"   
        exitFailure
    putStrLn $ show (search (BTree.Contains (min,max)) gist)

executeOperationR :: GiST RTree.Predicate (Int,Int) -> Flag -> String -> IO()
executeOperationR gist (Insert s) file  = do
    let key = read s :: (Int,Int)
    save (insert (key, RTree.Equals key) (2,4) gist) file 
executeOperationR gist (Delete s) file = do
    let key = read s :: (Int,Int) 
    save (delete (key, RTree.Equals key) (2,4) gist) file 
executeOperationR gist (Search s) file = do
    let ((minx,maxy),(maxx,miny)) = read s :: ((Int,Int),(Int,Int))
    when (minx > maxy || miny > maxy) $ do
        putStrLn "usage for RTree : main <-i key|-d key|-s ((minx,maxy),(maxx,miny))>"   
        exitFailure
    putStrLn $ show (search (RTree.Contains ((minx,maxy),(maxx,miny))) gist)
