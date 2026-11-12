module Arguments (Arguments (..), readArguments) where

import Data.Word (Word64)
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)

data Arguments = Arguments
  { argumentCount :: !Int
  , argumentNodes :: !Int
  , argumentSeed :: !Word64
  }

parseDecimal :: String -> Integer -> Integer -> String -> Either String Integer
parseDecimal name lower upper text
  | null text || any (\character -> character < '0' || character > '9') text =
      Left (name ++ " must contain decimal digits only; received " ++ show text)
  | otherwise = case readMaybe text of
      Nothing -> Left (name ++ " could not be parsed as an integer: " ++ show text)
      Just value
        | value < lower || value > upper ->
            Left (name ++ " must be between " ++ show lower ++ " and " ++ show upper
                  ++ "; received " ++ show value)
        | otherwise -> Right value

parseArguments :: [String] -> Either String Arguments
parseArguments arguments = case arguments of
  [countText, nodesText, seedText] -> do
    count <- parseDecimal "COUNT" 1 2147483647 countText
    nodes <- parseDecimal "NODES" 1 1024 nodesText
    seed <- parseDecimal "SEED" 0 4294967295 seedText
    pure (Arguments (fromInteger count) (fromInteger nodes) (fromInteger seed))
  _ -> Left ("expected exactly COUNT NODES SEED; received " ++ show arguments)

readArguments :: IO Arguments
readArguments = do
  arguments <- getArgs
  either die pure (parseArguments arguments)
