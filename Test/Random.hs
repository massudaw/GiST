{-# LANGUAGE MultiParamTypeClasses
    #-}

module Main where

import System.IO
import System.Exit
import System.Random
import Data.GiST.GiST
import qualified Data.GiST.BTree as BTree
import qualified Data.GiST.RTree as RTree
import Control.Monad(when)
import System.Environment(getArgs)
import System.Console.GetOpt
import qualified Data.Text.IO as TIO
import qualified Data.Text as T


-- | A small program that allows the user to add any number of random elements to a GiST and saves the resulting tree in the
-- "RandomBTree.txt" or "RandomRTree.txt" depending on the predicate type
-- The GiST is written after every insert
main    :: IO()
main =  do
    args <- getArgs  
    let (flags, nonOpt, msgs) = getOpt RequireOrder options args
    when (length flags /=1) $ do 
        putStrLn "usage : main <-b|-r> max_range num_inserts" 
        exitFailure
    when (length nonOpt /= 2) $ do
        putStrLn "usage : main <-b|-r> max_range num_inserts"
        exitFailure
    if (head flags == BTree ) then do
        let gist = empty :: GiST BTree.Predicate Int
        let file = "BTreeRandom.txt"
        save gist file
        g <- newStdGen
        executeOperationB file (read $ nonOpt!!0) (read $ nonOpt!!1) g
    else do
        let gist = empty :: GiST RTree.Predicate (Int,Int)
        let file = "RTreeRandom.txt"
        save gist file
        g <- newStdGen
        executeOperationR file (read $ nonOpt!!0) (read $ nonOpt!!1) g
    
    
    
data Flag = BTree | RTree deriving (Eq)

options :: [OptDescr Flag]
options = [
    Option ['b'] ["btree"] (NoArg BTree)  "use BTree GiST",
    Option ['r'] ["rtree"] (NoArg RTree)  "use RTree GiST"
  ]
   
    
    
executeOperationB :: String -> Int -> Int -> StdGen -> IO()
executeOperationB _ _ 0 _ = return()
executeOperationB file max num gen = do     
    gist <- (load file :: IO (GiST BTree.Predicate Int))
    let (key,g) = randomR (1,max) gen
    putStrLn $ show $ length $ getEntries gist
    save (insert (key, BTree.Equals key) (3,6) gist) file
    executeOperationB file max (num-1) g

executeOperationR :: String -> Int -> Int -> StdGen -> IO()
executeOperationR _ _ 0 _ = return()
executeOperationR file max num gen  = do
    gist <- (load file :: IO (GiST RTree.Predicate (Int,Int)))
    let (x,g) = randomR (1,max) gen
    let (y,g2) = randomR (1,max) g
    putStrLn $ show $ length $ getEntries gist
    save (insert ((x,y), RTree.Equals (x,y)) (3,6) gist) file
    executeOperationR file max (num-1) g2
