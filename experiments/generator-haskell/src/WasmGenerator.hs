module WasmGenerator
  ( Signature (..), BlockType (..), Instr (..), Function (..), WasmModule (..),
    Config (..), GenError (..), ChoiceSource (..),
    sizeConfig, generateModule, generateSample, replayModule
  ) where

import Data.Word (Word64)
import qualified Generator
import qualified SequenceOps
import qualified Word64Ops

-- Counts describe homogeneous I32 stacks, including empty and multiple results.
data Signature = Signature !Int !Int
data BlockType = EmptyBlock | ValueBlock | TypeBlock !Int

data Instr
  = IConst !Int | ILocalGet !Int | ILocalSet !Int | ILocalTee !Int
  | IAdd | ISub | IMul | INop | IDrop
  | IBlock BlockType [Instr] | ILoop BlockType [Instr]
  | IIf BlockType [Instr] [Instr] | ICall !Int

data Function = FunctionBody !Int !Int [Instr]
data WasmModule = ConstructedModule [Signature] [Function] [Int] (Maybe Int)

data Config = Config
  { maxTypes :: !Int, maxFunctions :: !Int, maxParameters :: !Int,
    maxResults :: !Int, maxLocals :: !Int, maxExports :: !Int,
    instructionBudget :: !Int
  }

data GenError
  = InvalidConfig | InvalidBound !Int | TapeExhausted !Int
  | ChoiceOutOfRange !Int !Int | UnusedChoices !Int | InvalidIndex !Int

data ChoiceSource = Seeded !Word64 | Replay [Int]

-- Every request consumes a value, even for bound one. Replay never takes modulo.
choose :: Int -> ChoiceSource -> Either GenError (Int, ChoiceSource)
choose bound source
  | bound <= 0 = Left (InvalidBound bound)
  | otherwise = case source of
      Seeded seed -> case Generator.choose bound seed of
        (value, next) -> Right (value, Seeded next)
      Replay [] -> Left (TapeExhausted bound)
      Replay (value : rest)
        | value < 0 || value >= bound -> Left (ChoiceOutOfRange bound value)
        | otherwise -> Right (value, Replay rest)

atIndex :: Int -> [a] -> Either GenError a
atIndex index values = case values of
  [] -> Left (InvalidIndex index)
  value : rest -> if index == 0 then Right value else atIndex (index - 1) rest

select :: [a] -> ChoiceSource -> Either GenError (a, ChoiceSource)
select values source = do
  (index, next) <- choose (length values) source
  value <- atIndex index values
  Right (value, next)

sizeConfig :: Int -> Config
sizeConfig size = Config size size size size size size size

-- Check with Integer before Int arithmetic/allocation. The native platform is 64-bit.
validConfig :: Config -> Bool
validConfig config =
  let fields = [maxTypes config, maxFunctions config, maxParameters config,
                maxResults config, maxLocals config, maxExports config, instructionBudget config]
      limit = 9223372036854775807 :: Integer
      parameters = toInteger (maxParameters config)
      results = toInteger (maxResults config)
      budget = toInteger (instructionBudget config)
  in all (\value -> value >= 0 && toInteger value < limit) fields
     && parameters + toInteger (maxLocals config) < limit
     && parameters + (budget + 1) * max 1 results < limit
     && 16 + toInteger (maxFunctions config) + 3 * toInteger (maxTypes config) < limit

makeSignatures :: [()] -> Config -> ChoiceSource -> Either GenError ([Signature], ChoiceSource)
makeSignatures [] _ source = Right ([], source)
makeSignatures (_ : rest) config source = do
  (parameters, next) <- choose (maxParameters config + 1) source
  (results, middle) <- choose (maxResults config + 1) next
  (signatures, final) <- makeSignatures rest config middle
  Right (Signature parameters results : signatures, final)

makeIndices :: [()] -> Int -> ChoiceSource -> Either GenError ([Int], ChoiceSource)
makeIndices [] _ source = Right ([], source)
makeIndices (_ : rest) bound source = do
  (index, next) <- choose bound source
  (indices, final) <- makeIndices rest bound next
  Right (index : indices, final)

functionSignatures :: [Int] -> [Signature] -> Either GenError [Signature]
functionSignatures [] _ = Right []
functionSignatures (index : rest) types = do
  signature <- atIndex index types
  signatures <- functionSignatures rest types
  Right (signature : signatures)

data Action
  = Stop | Constant | GetLocal | SetLocal | TeeLocal | Add | Sub | Mul | Nop | Drop
  | Call !Int !Int !Int
  | Block BlockType !Int !Int | Loop BlockType !Int !Int | If BlockType !Int !Int

callActions :: [Signature] -> Int -> Int -> [Action]
callActions [] _ _ = []
callActions (Signature parameters results : rest) index stack =
  (if parameters <= stack then [Call index parameters results] else [])
  ++ callActions rest (index + 1) stack

blockActions :: BlockType -> Int -> Int -> Int -> [Action]
blockActions block parameters results stack =
  (if parameters <= stack then [Block block parameters results, Loop block parameters results] else [])
  ++ (if parameters < stack then [If block parameters results] else [])

typeActions :: [Signature] -> Int -> Int -> [Action]
typeActions [] _ _ = []
typeActions (Signature parameters results : rest) index stack =
  blockActions (TypeBlock index) parameters results stack ++ typeActions rest (index + 1) stack

actions :: Int -> [Signature] -> [Signature] -> Int -> [Action]
actions available types signatures stack =
  [Stop, Constant, Nop]
  ++ (if stack > 0 then [Drop] else [])
  ++ (if stack > 1 then [Add, Sub, Mul] else [])
  ++ (if available > 0 then [GetLocal] else [])
  ++ (if available > 0 && stack > 0 then [SetLocal, TeeLocal] else [])
  ++ callActions signatures 0 stack
  ++ blockActions EmptyBlock 0 0 stack
  ++ blockActions ValueBlock 0 1 stack
  ++ typeActions types 0 stack

-- Fuel-zero and Stop construct the required stack without making random choices.
finishStack :: Int -> Int -> [Instr]
finishStack stack target =
  if stack > target then SequenceOps.replicate (stack - target) IDrop
  else SequenceOps.replicate (target - stack) (IConst 0)

-- Shared budget is returned from children to siblings; it is never duplicated.
-- Structural fuel establishes termination for the actual translated recursion.
generateCode :: [()] -> Int -> Int -> [Signature] -> [Signature] -> Int -> Int
             -> ChoiceSource -> Either GenError ([Instr], Int, ChoiceSource)
generateCode [] budget _ _ _ stack target source = Right (finishStack stack target, budget, source)
generateCode (_ : fuel) budget available types signatures stack target source
  | budget == 0 = Right (finishStack stack target, 0, source)
  | otherwise = do
      (action, next) <- select (actions available types signatures stack) source
      case action of
        Stop -> Right (finishStack stack target, budget - 1, next)
        Constant -> do
          (value, middle) <- choose 4294967296 next
          continueCode fuel (budget - 1) available types signatures (stack + 1) target [IConst value] middle
        Nop -> continueCode fuel (budget - 1) available types signatures stack target [INop] next
        Drop -> continueCode fuel (budget - 1) available types signatures (stack - 1) target [IDrop] next
        Add -> continueCode fuel (budget - 1) available types signatures (stack - 1) target [IAdd] next
        Sub -> continueCode fuel (budget - 1) available types signatures (stack - 1) target [ISub] next
        Mul -> continueCode fuel (budget - 1) available types signatures (stack - 1) target [IMul] next
        GetLocal -> do
          (index, middle) <- choose available next
          continueCode fuel (budget - 1) available types signatures (stack + 1) target [ILocalGet index] middle
        SetLocal -> do
          (index, middle) <- choose available next
          continueCode fuel (budget - 1) available types signatures (stack - 1) target [ILocalSet index] middle
        TeeLocal -> do
          (index, middle) <- choose available next
          continueCode fuel (budget - 1) available types signatures stack target [ILocalTee index] middle
        Call index parameters results ->
          continueCode fuel (budget - 1) available types signatures (stack - parameters + results) target [ICall index] next
        Block block parameters results -> do
          (body, remaining, middle) <- generateCode fuel (budget - 1) available types signatures parameters results next
          continueCode fuel remaining available types signatures (stack - parameters + results) target [IBlock block body] middle
        Loop block parameters results -> do
          (body, remaining, middle) <- generateCode fuel (budget - 1) available types signatures parameters results next
          continueCode fuel remaining available types signatures (stack - parameters + results) target [ILoop block body] middle
        If block parameters results -> do
          (yes, afterYes, middle) <- generateCode fuel (budget - 1) available types signatures parameters results next
          (no, afterNo, final) <- generateCode fuel afterYes available types signatures parameters results middle
          continueCode fuel afterNo available types signatures (stack - parameters - 1 + results) target [IIf block yes no] final

continueCode :: [()] -> Int -> Int -> [Signature] -> [Signature] -> Int -> Int -> [Instr]
             -> ChoiceSource -> Either GenError ([Instr], Int, ChoiceSource)
continueCode fuel budget available types signatures stack target prefix source = do
  (suffix, remaining, final) <- generateCode fuel budget available types signatures stack target source
  Right (prefix ++ suffix, remaining, final)

makeFunctions :: [Int] -> Config -> [Signature] -> [Signature] -> ChoiceSource
              -> Either GenError ([Function], ChoiceSource)
makeFunctions [] _ _ _ source = Right ([], source)
makeFunctions (index : rest) config types signatures source = do
  Signature parameters results <- atIndex index types
  (locals, next) <- choose (maxLocals config + 1) source
  (body, _, middle) <- generateCode (SequenceOps.replicate (instructionBudget config) ())
    (instructionBudget config) (parameters + locals) types signatures 0 results next
  (functions, final) <- makeFunctions rest config types signatures middle
  Right (FunctionBody index locals body : functions, final)

startIndices :: [Signature] -> Int -> [Int]
startIndices [] _ = []
startIndices (Signature parameters results : rest) index =
  (if parameters == 0 && results == 0 then [index] else []) ++ startIndices rest (index + 1)

-- Type-only and completely empty modules are valid choices, without invalid indices.
generateModule :: Config -> ChoiceSource -> Either GenError (WasmModule, ChoiceSource)
generateModule config source
  | not (validConfig config) = Left InvalidConfig
  | otherwise = do
      (typeCount, next) <- choose (maxTypes config + 1) source
      (types, afterTypes) <- makeSignatures (SequenceOps.replicate typeCount ()) config next
      (functionCount, afterCount) <- choose (if typeCount == 0 then 1 else maxFunctions config + 1) afterTypes
      (indices, afterIndices) <- makeIndices (SequenceOps.replicate functionCount ()) typeCount afterCount
      signatures <- functionSignatures indices types
      (functions, afterFunctions) <- makeFunctions indices config types signatures afterIndices
      (exportCount, afterExports) <- choose (if functionCount == 0 then 1 else maxExports config + 1) afterFunctions
      (exports, afterTargets) <- makeIndices (SequenceOps.replicate exportCount ()) functionCount afterExports
      (start, final) <- select (Nothing : map Just (startIndices signatures 0)) afterTargets
      Right (ConstructedModule types functions exports start, final)

generateSample :: Int -> Config -> Word64 -> Either GenError WasmModule
generateSample index config seed
  | index < 0 = Left InvalidConfig
  | otherwise = do
      (value, _) <- generateModule config (Seeded (Word64Ops.add seed (fromIntegral index)))
      Right value

-- Successful replay consumes the whole tape; an unused suffix is an error.
replayModule :: Config -> [Int] -> Either GenError WasmModule
replayModule config tape = do
  (value, final) <- generateModule config (Replay tape)
  case final of
    Replay [] -> Right value
    Replay rest -> Left (UnusedChoices (length rest))
    Seeded _ -> Left InvalidConfig
