module Main (main) where

import Data.Word (Word64)
import System.Environment (getArgs)
import System.Exit (die)
import Text.Read (readMaybe)
import WasmGenerator (Config (..), GenError (..), WasmModule, sizeConfig, generateSample, replayModule)
import WasmJson (renderModule)

data Request = Sample !Int Config !Word64 | ReplayFile Config FilePath

decimal :: String -> Integer -> Integer -> String -> Either String Integer
decimal name lower upper input
  | null input || any (\character -> character < '0' || character > '9') input =
      Left (name ++ " must contain decimal digits only: " ++ show input)
  | otherwise = case readMaybe input of
      Nothing -> Left (name ++ " is not a decimal integer: " ++ show input)
      Just number | number < lower || number > upper ->
        Left (name ++ " must be between " ++ show lower ++ " and " ++ show upper ++ ": " ++ show number)
      Just number -> Right number

configArguments :: [String] -> Either String Config
configArguments [types, functions, parameters, results, locals, exports, fuel] = do
  values <- sequence [decimal name 0 1000000 value | (name, value) <- zip
    ["TYPES", "FUNCS", "PARAMS", "RESULTS", "LOCALS", "EXPORTS", "FUEL"]
    [types, functions, parameters, results, locals, exports, fuel]]
  case map fromInteger values of
    [t, f, p, r, l, e, b] -> Right (Config t f p r l e b)
    _ -> Left "internal configuration field-count mismatch"
configArguments values = Left ("expected TYPES FUNCS PARAMS RESULTS LOCALS EXPORTS FUEL; received " ++ show values)

-- Conservative allocation estimate and recursion limit are CLI safety policy only.
checkResources :: Int -> Config -> Either String ()
checkResources count config
  | instructionBudget config > 512 = Left "FUEL exceeds the CLI recursion safety limit 512"
  | estimate > 10000000 = Left ("requested batch exceeds the CLI allocation estimate 10000000: " ++ show estimate)
  | otherwise = Right ()
  where
    budget = toInteger (instructionBudget config)
    stack = toInteger (maxParameters config) + (budget + 1) * max 1 (toInteger (maxResults config))
    estimate = toInteger count * (1 + toInteger (maxTypes config) *
      (1 + toInteger (maxParameters config) + toInteger (maxResults config)) + toInteger (maxExports config)
      + toInteger (maxFunctions config) * (1 + toInteger (maxLocals config) + budget + (3 * budget + 1) * stack))

arguments :: [String] -> Either String Request
arguments [countText, sizeText, seedText] = do
  count <- decimal "COUNT" 1 1000000 countText
  size <- decimal "SIZE" 0 1000000 sizeText
  seed <- decimal "SEED" 0 18446744073709551615 seedText
  let config = sizeConfig (fromInteger size)
  checkResources (fromInteger count) config
  Right (Sample (fromInteger count) config (fromInteger seed))
arguments ("sample" : countText : seedText : fields) = do
  count <- decimal "COUNT" 1 1000000 countText
  seed <- decimal "SEED" 0 18446744073709551615 seedText
  config <- configArguments fields
  checkResources (fromInteger count) config
  Right (Sample (fromInteger count) config (fromInteger seed))
arguments ["replay", t, f, p, r, l, e, b, path] = do
  config <- configArguments [t, f, p, r, l, e, b]
  checkResources 1 config
  Right (ReplayFile config path)
arguments values = Left ("expected COUNT SIZE SEED, sample COUNT SEED TYPES FUNCS PARAMS RESULTS LOCALS EXPORTS FUEL, "
  ++ "or replay TYPES FUNCS PARAMS RESULTS LOCALS EXPORTS FUEL TAPE_FILE; received " ++ show values)

errorMessage :: GenError -> String
errorMessage problem = case problem of
  InvalidConfig -> "invalid configuration: negative field/sample index or unsafe 64-bit Int arithmetic"
  InvalidBound bound -> "invalid exclusive choice bound: " ++ show bound
  TapeExhausted bound -> "replay tape exhausted while requesting exclusive bound " ++ show bound
  ChoiceOutOfRange bound value -> "replay choice " ++ show value ++ " outside [0," ++ show bound ++ ")"
  UnusedChoices count -> "replay tape contains " ++ show count ++ " unused choices"
  InvalidIndex index -> "internal context index is invalid: " ++ show index

writeResult :: Either GenError WasmModule -> IO ()
writeResult result = case result of
  Left problem -> die (errorMessage problem)
  Right value -> putStrLn (renderModule value)

writeModules :: Int -> Int -> Config -> Word64 -> IO ()
writeModules index count config seed
  | index == count = pure ()
  | otherwise = do
      writeResult (generateSample index config seed)
      writeModules (index + 1) count config seed

readChoice :: String -> Either String Int
readChoice text = do
  let digits = case text of
        '-' : rest -> rest
        _ -> text
  magnitude <- decimal "tape magnitude" 0 9223372036854775808 digits
  let value = if take 1 text == "-" then negate magnitude else magnitude
  if value > 9223372036854775807
    then Left ("tape token exceeds signed 64-bit Int: " ++ show text)
    else Right (fromInteger value)

main :: IO ()
main = do
  values <- getArgs
  case arguments values of
    Left message -> die message
    Right (Sample count config seed) -> writeModules 0 count config seed
    Right (ReplayFile config path) -> do
      contents <- readFile path
      case traverse readChoice (words contents) of
        Left message -> die message
        Right tape -> writeResult (replayModule config tape)
