module SequenceOps (replicate) where

import qualified Prelude

-- Keep the native library operation explicit at the translation boundary.
replicate :: Prelude.Int -> a -> [a]
replicate = Prelude.replicate
