module Word64Ops (add, multiply) where

import Data.Word (Word64)

add :: Word64 -> Word64 -> Word64
add left right = left + right

multiply :: Word64 -> Word64 -> Word64
multiply left right = left * right
