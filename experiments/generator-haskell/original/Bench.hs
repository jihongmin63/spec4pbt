{-# LANGUAGE BangPatterns #-}

module Main (main) where

import Arguments (Arguments (..), readArguments)
import Control.Exception (evaluate)
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import Generator (generateSample, inspectExpr)

runSamples :: Int -> Int -> Int -> Word64 -> Word64 -> Word64 -> IO (Word64, Word64)
runSamples !index !count !nodes !seed !totalNodes !checksum
  | index == count = pure (totalNodes, checksum)
  | otherwise = do
      (!actualNodes, !digest) <- evaluate (inspectExpr (generateSample index nodes seed))
      let !nextTotal = totalNodes + fromIntegral actualNodes
          !nextChecksum = checksum * 1000003 + digest
      runSamples (index + 1) count nodes seed nextTotal nextChecksum

main :: IO ()
main = do
  arguments <- readArguments
  let !count = argumentCount arguments
      !nodes = argumentNodes arguments
      !seed = argumentSeed arguments
  start <- getMonotonicTimeNSec
  (!totalNodes, !checksum) <- runSamples 0 count nodes seed 0 0
  stop <- getMonotonicTimeNSec
  let output = showString "{\"count\":" . shows count
        . showString ",\"nodes\":" . shows nodes
        . showString ",\"seed\":" . shows seed
        . showString ",\"total_nodes\":" . shows totalNodes
        . showString ",\"checksum\":" . shows checksum
        . showString ",\"elapsed_ns\":" . shows (stop - start) . showChar '}'
  putStrLn (output "")
