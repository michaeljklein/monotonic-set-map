{-# LANGUAGE BinaryLiterals #-}

module Data.Word4 where

import Data.Bits (Bits(..))
import Data.Word
import Test.QuickCheck hiding ((.&.))

-- | `Word8` where the 4 most significant bits are zero.
newtype Word4 = Word4 { unWord4 :: Word8 } deriving (Eq, Ord, Show)

instance Arbitrary Word4 where
  arbitrary = Word4 . (.&. 0b1111) <$> arbitrary

