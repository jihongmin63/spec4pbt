module Main (main) where

import Arguments (Arguments (..), readArguments)
import Data.Word (Word64)
import Generator (Type (..), generateSample, inspectExpr, renderExpr, renderType)
import System.Exit (die)

writeSamples :: Int -> Int -> Int -> Word64 -> IO ()
writeSamples index count nodes seed
  | index == count = pure ()
  | otherwise = case generateSample index nodes seed of
      Nothing -> die ("generator exhausted fuel: index=" ++ show index
                      ++ ", nodes=" ++ show nodes ++ ", seed=" ++ show seed)
      Just expression -> do
        let target = if even index then IntType else BoolType
            (actualNodes, digest) = inspectExpr expression
            output = showString "{\"index\":" . shows index . showString ",\"type\":\""
              . showString (renderType target) . showString "\",\"expr\":"
              . renderExpr expression . showString ",\"nodes\":" . shows actualNodes
              . showString ",\"digest\":" . shows digest . showChar '}'
        putStrLn (output "")
        writeSamples (index + 1) count nodes seed

main :: IO ()
main = do
  arguments <- readArguments
  writeSamples 0 (argumentCount arguments) (argumentNodes arguments) (argumentSeed arguments)
