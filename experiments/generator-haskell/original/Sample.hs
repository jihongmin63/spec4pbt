module Main (main) where

import Arguments (Arguments (..), readArguments)
import Data.Word (Word64)
import Generator (Type (..), generateSample, renderExpr, renderType)

writeSamples :: Int -> Int -> Int -> Word64 -> IO ()
writeSamples index count nodes seed
  | index == count = pure ()
  | otherwise = do
      let target = if even index then IntType else BoolType
          expression = generateSample index nodes seed
          output = showString "{\"index\":" . shows index . showString ",\"type\":\""
            . showString (renderType target) . showString "\",\"expr\":"
            . renderExpr expression . showChar '}'
      putStrLn (output "")
      writeSamples (index + 1) count nodes seed

main :: IO ()
main = do
  arguments <- readArguments
  writeSamples 0 (argumentCount arguments) (argumentNodes arguments) (argumentSeed arguments)
