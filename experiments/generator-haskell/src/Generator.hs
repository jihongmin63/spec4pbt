{-# LANGUAGE BangPatterns #-}

module Generator
  ( Type (..), Expr (..), nextWord, choose, generate, generateSample, inspectExpr,
    renderExpr, renderType
  ) where

import Data.Bits (shiftR, xor)
import Data.Word (Word64)
import qualified Word64Ops
import qualified SequenceOps

data Type = IntType | BoolType

-- Spell out derived equality to avoid GHC's unboxed enum-tag primitives.
instance Eq Type where
  IntType == IntType = True
  BoolType == BoolType = True
  _ == _ = False

data Expr
  = IntLiteral !Int
  | BoolLiteral !Bool
  | Variable !Int
  | Negate !Expr
  | Not !Expr
  | Add !Expr !Expr
  | Equal !Expr !Expr
  | If !Expr !Expr !Expr
  | Let !Type !Expr !Expr

-- SplitMix64's state increment and mixing arithmetic wrap modulo 2^64.
nextWord :: Word64 -> (Word64, Word64)
nextWord state =
  let !next = Word64Ops.add state 0x9e3779b97f4a7c15
      !first = Word64Ops.multiply (next `xor` (next `shiftR` 30)) 0xbf58476d1ce4e5b9
      !second = Word64Ops.multiply (first `xor` (first `shiftR` 27)) 0x94d049bb133111eb
      !value = second `xor` (second `shiftR` 31)
  in (value, next)

-- Bounds are positive by construction. Modulo selection has tiny finite bias.
choose :: Int -> Word64 -> (Int, Word64)
choose bound state =
  case nextWord state of
    (value, next) -> (fromIntegral (value `mod` fromIntegral bound), next)

matchingIndices :: Type -> [Type] -> [Int]
matchingIndices target context = [index | (index, actual) <- zip [0 .. length context - 1] context, actual == target]

generateLiteral :: Type -> Word64 -> (Expr, Word64)
generateLiteral target state =
  case target of
    IntType -> case choose 256 state of
      (number, next) -> (IntLiteral number, next)
    BoolType -> case choose 2 state of
      (boolean, next) -> (BoolLiteral (boolean == 1), next)

generateLeaf :: Type -> [Type] -> Word64 -> (Expr, Word64)
generateLeaf target context state =
  case matchingIndices target context of
    [] -> generateLiteral target state
    indices -> case choose 2 state of
      (0, next) -> generateLiteral target next
      (_, next) -> case choose (length indices) next of
        (offset, final) -> (Variable (indices !! offset), final)

-- Each construction consumes one unit of structural fuel before recursing.
generateUnary :: [()] -> Type -> [Type] -> Int -> Word64 -> Maybe (Expr, Word64)
generateUnary fuel target context nodes state =
  case generate fuel target context (nodes - 1) state of
    Nothing -> Nothing
    Just (child, next) -> case target of
      IntType -> Just (Negate child, next)
      BoolType -> Just (Not child, next)

generateBinary :: [()] -> Type -> [Type] -> Int -> Word64 -> Maybe (Expr, Word64)
generateBinary fuel target context nodes state =
  case choose (nodes - 2) state of
    (split, next) ->
      case generate fuel IntType context (split + 1) next of
        Nothing -> Nothing
        Just (left, middle) -> case generate fuel IntType context (nodes - split - 2) middle of
          Nothing -> Nothing
          Just (right, final) -> case target of
            IntType -> Just (Add left right, final)
            BoolType -> Just (Equal left right, final)

generateLet :: [()] -> Type -> [Type] -> Int -> Word64 -> Maybe (Expr, Word64)
generateLet fuel target context nodes state =
  case choose 2 state of
    (binderChoice, next) ->
      let !binder = if binderChoice == 0 then IntType else BoolType
      in case choose (nodes - 2) next of
        (split, divided) -> case generate fuel binder context (split + 1) divided of
          Nothing -> Nothing
          Just (rhs, middle) -> case generate fuel target (binder : context) (nodes - split - 2) middle of
            Nothing -> Nothing
            Just (body, final) -> Just (Let binder rhs body, final)

generateIf :: [()] -> Type -> [Type] -> Int -> Word64 -> Maybe (Expr, Word64)
generateIf fuel target context nodes state =
  case choose (nodes - 3) state of
    (first, next) -> case choose (nodes - first - 3) next of
      (second, divided) -> case generate fuel BoolType context (first + 1) divided of
        Nothing -> Nothing
        Just (condition, afterCondition) -> case generate fuel target context (second + 1) afterCondition of
          Nothing -> Nothing
          Just (yes, afterYes) -> case generate fuel target context (nodes - first - second - 3) afterYes of
            Nothing -> Nothing
            Just (no, final) -> Just (If condition yes no, final)

generate :: [()] -> Type -> [Type] -> Int -> Word64 -> Maybe (Expr, Word64)
generate [] _ _ _ _ = Nothing
generate (_ : fuel) target context nodes state
  | nodes == 1 = Just (generateLeaf target context state)
  | otherwise =
      let !families = if nodes == 2 then 1 else if nodes == 3 then 3 else 4
      in case choose families state of
        (0, next) -> generateUnary fuel target context nodes next
        (1, next) -> generateBinary fuel target context nodes next
        (2, next) -> generateLet fuel target context nodes next
        (_, next) -> generateIf fuel target context nodes next

-- Keep an actual AST boundary between construction and benchmark traversal.
{-# NOINLINE generateSample #-}
generateSample :: Int -> Int -> Word64 -> Maybe Expr
generateSample index nodes seed =
  let !target = if even index then IntType else BoolType
  in case generate (SequenceOps.replicate nodes ()) target [] nodes (Word64Ops.add seed (fromIntegral index)) of
    Nothing -> Nothing
    Just (expression, _) -> Just expression

combine :: Word64 -> Word64 -> Word64
combine hash value = Word64Ops.add (Word64Ops.multiply hash 1000003) value

inspectUnary :: Word64 -> Expr -> (Int, Word64)
inspectUnary tag child =
  case inspectExpr child of
    (!nodes, !digest) -> (nodes + 1, combine tag digest)

inspectBinary :: Word64 -> Expr -> Expr -> (Int, Word64)
inspectBinary tag left right =
  case inspectExpr left of
    (!leftNodes, !leftDigest) -> case inspectExpr right of
      (!rightNodes, !rightDigest) ->
        (leftNodes + rightNodes + 1, combine (combine tag leftDigest) rightDigest)

{-# NOINLINE inspectExpr #-}
inspectExpr :: Expr -> (Int, Word64)
inspectExpr expression = case expression of
  IntLiteral number -> (1, combine 1 (fromIntegral number))
  BoolLiteral boolean -> (1, combine 2 (if boolean then 1 else 0))
  Variable index -> (1, combine 3 (fromIntegral index))
  Negate child -> inspectUnary 4 child
  Not child -> inspectUnary 5 child
  Add left right -> inspectBinary 6 left right
  Equal left right -> inspectBinary 7 left right
  If condition yes no ->
    case inspectExpr condition of
      (!conditionNodes, !conditionDigest) -> case inspectExpr yes of
        (!yesNodes, !yesDigest) -> case inspectExpr no of
          (!noNodes, !noDigest) ->
            (1 + conditionNodes + yesNodes + noNodes,
             combine (combine (combine 8 conditionDigest) yesDigest) noDigest)
  Let binder rhs body ->
    inspectBinary (combine 9 (if binder == IntType then 0 else 1)) rhs body

renderType :: Type -> String
renderType target = case target of
  IntType -> "int"
  BoolType -> "bool"

renderUnary :: String -> Expr -> ShowS
renderUnary tag child =
  showString "[\"" . showString tag . showString "\"," . renderExpr child . showChar ']'

renderBinary :: String -> Expr -> Expr -> ShowS
renderBinary tag left right =
  showString "[\"" . showString tag . showString "\"," . renderExpr left
  . showChar ',' . renderExpr right . showChar ']'

renderExpr :: Expr -> ShowS
renderExpr expression = case expression of
  IntLiteral number -> showString "[\"int\"," . shows number . showChar ']'
  BoolLiteral boolean ->
    showString "[\"bool\"," . showString (if boolean then "true" else "false") . showChar ']'
  Variable index -> showString "[\"var\"," . shows index . showChar ']'
  Negate child -> renderUnary "neg" child
  Not child -> renderUnary "not" child
  Add left right -> renderBinary "add" left right
  Equal left right -> renderBinary "eq" left right
  If condition yes no ->
    showString "[\"if\"," . renderExpr condition . showChar ',' . renderExpr yes
    . showChar ',' . renderExpr no . showChar ']'
  Let binder rhs body ->
    showString "[\"let\",\"" . showString (renderType binder) . showString "\","
    . renderExpr rhs . showChar ',' . renderExpr body . showChar ']'
