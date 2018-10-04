{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lib where

import Data.Word
import Data.Word4
import Utils.Containers.Internal.StrictPair
import Control.Monad (ap, liftM2)
import Data.Function (fix)
import qualified Data.Set as S
import Data.Set.Internal (Set(..), powerSet, size, link)
import Test.QuickCheck
  ( Property
  , Arbitrary(..)
  , Testable(..)
  , (.&&.)
  , (===)
  , (==>)
  , counterexample
  , quickCheckAll
  )
import Data.Bits (Bits(..))
import Criterion
import Criterion.Main (defaultMain)
import Data.Functor.Identity
import Control.Comonad
import Control.Comonad.Cofree
import Data.Foldable
import Data.Maybe

-- | `mapMonotonicallyInc` can reduce the needed number of required applications
-- of the given function. For example, consider the following case:
--
-- @
--  mapMonotonicallyInc :: Set a -> Set ()
--  mapMonotonicallyInc (const ())
-- @
--
-- while @S.map (const ())@ takes @O(n log n)@ time, the above
-- takes the ideal: @O(1)@ constant time.
--
-- The following case also exhibits this behavior:
--
-- @
--  mapMonotonicallyInc ceiling $
--    fromDistinctAscList
--      [0.64, 0.75, 0.95]
-- @
--

---- | `mapMonotonic` is a misnomer, it should actually
---- be called @mapStrictlyMonotonic@ or @mapMonotonic'@.
----
---- This is the _real_ `mapMonotonic`, it has to throw out duplicates.
--mapMonotonicallyIncreasing :: Ord b => (a -> b) -> Set a -> Set b
--mapMonotonicallyIncreasing _ Tip = Tip
--mapMonotonicallyIncreasing f ~(Bin sx x l r) = (f x) -> if equal l, then we have:

-- | Property that one is less than another, with `counterexample`
lt :: (Ord a, Show a) => a -> a -> Property
lt x y =
  counterexample (show x ++ interpret res ++ show y) res
  where
    res = x < y
    interpret True  = " <  "
    interpret False = " >= "

-- | Property that one is less than or equal to another, with `counterexample`
leq :: (Ord a, Show a) => a -> a -> Property
leq x y =
  counterexample (show x ++ interpret res ++ show y) res
  where
    res = x <= y
    interpret True  = " <= "
    interpret False = " >  "


-- | Property that the arguments are non-equal, with `counterexample`
infix 4 /==
(/==) :: (Eq a, Show a) => a -> a -> Property
x /== y =
  counterexample (show x ++ interpret res ++ show y) res
  where
    res = x /= y
    interpret True  = " /= "
    interpret False = " == "

-- | The `sum` of a set is not monotonically increasing:
--
-- @
--  fromList [1,4]
--  fromList [2]
--  5 >  2
-- @
--
sumNotMonoInc :: ()
sumNotMonoInc = ()

-- | Apply the function repeatedly until it returns `Nothing`.
-- Return the last `Just` result or the input if there is none.
{-# INLINE fixMaybeOn #-}
fixMaybeOn :: (a -> Maybe a) -> a -> a
fixMaybeOn = fix ((ap =<<) . (flip maybe .))

-- | Recalculate the size given a root and its two immediate sub-`Set`s
{-# INLINE resize #-}
resize :: a -> Set a -> Set a -> Set a
resize = resizeF Bin

-- | Recalculate the size a la `resize`,
-- also given a constructor to produce the result
{-# INLINE resizeF #-}
resizeF :: (Int -> a -> Set a -> Set a -> b) -> a -> Set a -> Set a -> b
resizeF f x ls rs = f (1 + size ls + size rs) x ls rs

-- | If the root of the tree is equal to the root of the left subtree,
-- then so are the elements of the left subtree's right subtree.
-- We join them with their new sizes.
{-# INLINE joinLeft #-}
joinLeft :: Eq a => Set a -> Maybe (Set a)
joinLeft (Bin _ x (Bin _ y ls _) rs)
  | x == y = Just $ resize x ls rs
joinLeft _ = Nothing

-- | See `joinLeft`
{-# INLINE joinRight #-}
joinRight :: Eq a => Set a -> Maybe (Set a)
joinRight (Bin _ x ls (Bin _ y _ rs))
  | x == y = Just $ resize x ls rs
joinRight _ = Nothing

-- | `joinRight` as many times as possible, then do the same with `joinLeft`
{-# INLINE firstJoins #-}
firstJoins :: Eq a => Set a -> Set a
firstJoins = fixMaybeOn joinLeft . fixMaybeOn joinRight

-- | Reimplementation of `firstJoins`
joinLrs :: Eq a => Set a -> Set a
joinLrs Tip = Tip
joinLrs ~(Bin _ x ls rs) = loop x ls rs
  where
    loop y Tip rs' = Bin (1 + size rs') y Tip (joinRights rs')
    loop y ys@(~(Bin _ z ls' _)) rs' =
      if y == z
        then loop y ls' rs'
        else resizeF (const joinRightsLoop) y ys rs'

-- | Join equal values along right sub-`Set`s
{-# INLINE joinRights #-}
joinRights :: Eq a => Set a -> Set a
joinRights Tip = Tip
joinRights ~(Bin _ x ls rs) = joinRightsLoop x ls rs

-- | `joinRights` on a known non-`Tip` `Set`
joinRightsLoop :: Eq a => a -> Set a -> Set a -> Set a
joinRightsLoop x ls Tip = Bin (1 + size ls) x ls Tip
joinRightsLoop x ls xs@(~(Bin sz y _ rs)) =
  if x == y
    then joinRightsLoop x ls rs
    else resize x ls xs

-- | Join equal elements
{-# INLINE joins #-}
joins :: Eq a => Set a -> Set a
joins Tip = Tip
joins ~(Bin _ x ls rs) = joinsF x ls rs

-- | `joins` on a known non-`Tip` `Set`
joinsF :: Eq a => a -> Set a -> Set a -> Set a
joinsF x ls rs =
  case ls of
    Tip ->
      case rs of
        Tip -> S.singleton x
        ~(Bin _ ry rls rrs) ->
          if x == ry
            then joinsF x ls rrs
            else link ry (joinsF x ls rls) rrs
    ~(Bin _ ly lls lrs) ->
      if x == ly
        then case rs of
               Tip -> link x lls Tip -- insertMax x lls
               ~(Bin _ ry rls rrs) ->
                 link
                   x
                   (joins lls)
                   (if x == ry
                      then joins rrs
                      else joinsF ry rls rrs)
        else case rs of
               Tip -> link x ls Tip -- insertMax x ls
               ~(Bin _ ry rls rrs) ->
                 link
                   x
                   (joinsF ly lls lrs)
                   (if x == ry
                      then joins rrs
                      else joinsF ry rls rrs)

-- | `mapLevels` `firstJoins`
{-# INLINE joins'' #-}
joins'' :: Eq a => Set a -> Set a
joins'' = mapLevels firstJoins

-- | `mapLevels` `joinLrs`
{-# INLINE joins' #-}
joins' :: Eq a => Set a -> Set a
joins' = mapLevels joinLrs

-- Hmm, how can we map over the levels?
--   Would it be better to record the differences in size, then collect those up the tree?
--   Mmm, that could require a stack frame for each subtree until it reaches the leaves..
mapLevels :: (Set a -> Set a) -> Set a -> Set a
mapLevels f x =
  case f x of
    Tip -> Tip
    ~(Bin sz x ls rs) ->
      let ls' = mapLevels f ls
          rs' = mapLevels f rs
          sz' = 1 + size ls' + size rs'
       in Bin sz' x ls' rs'

-- | Using `joins`
mapMonotonicallyIncreasing :: Eq b => (a -> b) -> Set a -> Set b
mapMonotonicallyIncreasing = fmap joins . S.mapMonotonic

-- | Using `joins'`
mapMonotonicallyIncreasing' :: Eq b => (a -> b) -> Set a -> Set b
mapMonotonicallyIncreasing' = fmap joins' . S.mapMonotonic

-- | Using `joins''`
mapMonotonicallyIncreasing'' :: Eq b => (a -> b) -> Set a -> Set b
mapMonotonicallyIncreasing'' = fmap joins'' . S.mapMonotonic

-- easier to write (and hopefully much faster) `mapMonotonicallyIncreasing`:
--
-- mapMono :: Eq b => (a -> b) -> Set a -> Set b
-- mapMono _ Tip = Tip
-- mapMono f xs@(~(Bin sz x ls rs)) = mapMonoF x ls rs
--   case ls of
--     Tip ->
--       case rs of
--         Tip -> S.singleton $ f x
--         ~(Bin _ xr rls rrs) ->
--           let x' = f x
--               xr' = f xr
--            in if x' == xr'
--                 then mapMonoFR x' rrs -- ls is Tip and all ((== x') . f) rls
--                 else mapMonoF x' rls rrs
--     ~(Bin _ xl lls lrs) ->
--       let x' = f x
--           xl' = f xl
--        in if x' == xl'
--             then case rs -- lrs gets cut
--                        of
--                    Tip -> mapMonoFL x' lls
--                    ~(Bin _ xr rls rrs) ->
--                      let xr' = f xr
--                       in if x' == xr'
--                            then mapMonoF x' lls rrs
--                            else mapMonoFL x' lls `mergeLeq` mapMonoF xr' rls rrs
--             else case rs of
--                    Tip -> mapMonoFL xl' lls `mergeLeq` mapMonoFL x' lrs -- lls <= xl' <= lrs <= x'
--                    ~(Bin _ xr rls rrs) ->
--                      let xr' = f xr
--                       in if x' == xr'
--                            then mapMonoF xl' lls lrs `mergeLeq` mapMonoFR x' rrs
--                            else mapMonoFL xl' lls `mergeLeq` mapMonoFL x' lrs `mergeLeq`
--                                 mapMonoF xr' rls rrs
--   where
--     -- | `mapMono` specialized to `Bin`
--     mapMonoF :: b -> Set a -> Set a -> Set b
--     mapMonoF z Tip rz = mapMonoFR z rz
--     mapMonoF z lz Tip = mapMonoFL z lz -- hmm, at this point we know that lz is not tip..
--     mapMonoF z lz rz = undefined
--
--     -- | `mapMonoF`, where the right set is Tip
--     mapMonoFL :: b -> Set a -> Set b
--     mapMonoFL z lz = undefined
--
--     -- | `mapMonoF`, where the left set is Tip
--     mapMonoFR :: b -> Set a -> Set b
--     mapMonoFR z Tip = S.singleton $ f z
--     mapMonoFR z ~(Bin w wls wrs) = let w' = f w
--                                    in if z == w'
--                                          then mapMonoFR z wrs
--                                          else z <= fmap f wls < w' <= fmap f wrs
--
--     -- | Equivalent to `union`, but only needs an `Eq` constraint and
--     -- assumes @[lz] <= [rz]@
--     mergeLeq :: Set b -> Set b -> Set b
--     mergeLeq lz rz = undefined


-- | Logical implication
{-# INLINE impl #-}
impl :: Bool -> Bool -> Bool
impl x y = not x || y

-- | Get `Just` the first element of a `Set` and the rest of it or `Nothing`
{-# INLINE uncons #-}
uncons :: Ord a => Set a -> Maybe (a, Set a)
uncons Tip = Nothing
uncons ~(Bin _ x ls rs) = Just (x, S.union ls rs)


-- | `mapMonotonicallyIncreasing` with duplicates removed is equivalent to `S.map` for monotonically increasing functions
mapMonotonicHolds :: (Ord a, Ord b, Show a, Show b) => ((a -> b) -> Set a -> Set b) -> (a -> b) -> Set a -> Property
mapMonotonicHolds mapMonoInc' f xs =
  (and [(x < y) `impl` (f x <= f y) | x <- S.toList xs, y <- S.toList xs]) ==>
  (S.fromAscList (toList (mapMonoInc' f xs)) === S.map f xs)

-- | `mapMonotonicHolds` where the first element of a `Set`
-- replaces all elements not in the first `Set` and the rest are untouched.
mapMonotonicHoldsSubset :: (Ord a, Show a) => ((a -> a) -> Set a -> Set a) -> Set a -> Set a -> Property
mapMonotonicHoldsSubset mapMonoInc' xs =
  case uncons xs of
    Nothing -> mapMonotonicHolds mapMonoInc' id
    ~(Just (x, _)) ->
      mapMonotonicHolds mapMonoInc'
        (\y ->
           if y `S.member` xs
             then y
             else max x y)

-- | Infinite streams
newtype Stream a = Stream { runStream :: Cofree Identity a } deriving (Functor)

-- | Show the first 100 values
instance Show a => Show (Stream a) where
  show = show . take maxSize . toList
    where
      maxSize = 100

instance Arbitrary a => Arbitrary (Stream a) where
  arbitrary = Stream <$> liftM2 (:<) arbitrary (Identity . runStream <$> arbitrary)

instance Foldable Stream where
  foldMap f ~(Stream (x :< Identity xs)) = f x <> foldMap f xs

-- | Keep in `Set` if `True`
subsetBy :: Ord a => Stream Bool -> Set a -> Set a
subsetBy bs xs =
  S.fromAscList . catMaybes $
  zipWith
    (\b ->
       if b
         then Just
         else const Nothing)
    (toList bs)
    (S.toAscList xs)

-- | Use `subsetBy` to provide the first argument
withSubset :: Ord a => (Set a -> Set a -> b) -> Stream Bool -> Set a -> b
withSubset f bs xs = subsetBy bs xs `f` xs

-- | Subset-input properties
type SubsetProp a = Stream Bool -> Set a -> Property

-- | `mapMonotonicHoldsSubset` `mapMonotonicallyIncreasing` for `Word4`
prop_mapMonotonicHoldsSubsetWord4 :: SubsetProp Word4
prop_mapMonotonicHoldsSubsetWord4 = withSubset $ mapMonotonicHoldsSubset mapMonotonicallyIncreasing

-- | `mapMonotonicHoldsSubset` `mapMonotonicallyIncreasing` for `Word8`
prop_mapMonotonicHoldsSubsetWord8 :: SubsetProp Word8
prop_mapMonotonicHoldsSubsetWord8 = withSubset $ mapMonotonicHoldsSubset mapMonotonicallyIncreasing

-- | `mapMonotonicHoldsSubset` `mapMonotonicallyIncreasing'` for `Word4`
prop_mapMonotonicHoldsSubsetWord4' :: SubsetProp Word4
prop_mapMonotonicHoldsSubsetWord4' = withSubset $ mapMonotonicHoldsSubset mapMonotonicallyIncreasing'

-- | `mapMonotonicHoldsSubset` `mapMonotonicallyIncreasing'` for `Word8`
prop_mapMonotonicHoldsSubsetWord8' :: SubsetProp Word8
prop_mapMonotonicHoldsSubsetWord8' = withSubset $ mapMonotonicHoldsSubset mapMonotonicallyIncreasing'

-- | `mapMonotonicHoldsSubset` `mapMonotonicallyIncreasing''` for `Word4`
prop_mapMonotonicHoldsSubsetWord4'' :: SubsetProp Word4
prop_mapMonotonicHoldsSubsetWord4'' = withSubset $ mapMonotonicHoldsSubset mapMonotonicallyIncreasing''

-- | `mapMonotonicHoldsSubset` `mapMonotonicallyIncreasing''` for `Word8`
prop_mapMonotonicHoldsSubsetWord8'' :: SubsetProp Word8
prop_mapMonotonicHoldsSubsetWord8'' = withSubset $ mapMonotonicHoldsSubset mapMonotonicallyIncreasing''


countSubsetSums :: Int -> Int
countSubsetSums n = length . S.map sum . powerSet $ [1..n]

countSubsetSums2 :: Int -> Int
countSubsetSums2 n = length . S.map sum . powerSet . S.mapMonotonic (^2) $ [1..n]

countSubsetSums3 :: Int -> Int
countSubsetSums3 n = length . S.map sum . powerSet . S.mapMonotonic (^3) $ [1..n]

-- | Set up bench environment with:
--
-- @
--  let small = [1..100]
--      large = [1..2^10]
--      halfOverlapping = S.mapMonotonic (\x -> if even x then x + 1 else x) [1..2^20]
--  return (small, large, halfOverlapping)
-- @
--
setupEnv :: IO (Set Word8, Set Word16, Set Word32)
setupEnv = do
  let small = [1..100]
      large = [1..2^10]
      halfOverlapping = S.mapMonotonic (\x -> if even x then x + 1 else x) [1..2^20]
  return (small, large, halfOverlapping)

-- | Run benchmarks
runBenches :: IO ()
runBenches = defaultMain [
    env setupEnv $ \ ~(small, large, halfOverlapping) -> bgroup "main" [
      bgroup "joins" [
        bgroup "small" [
            bench "joins" $ nf joins small
          , bench "joins'" $ nf joins' small
          , bench "joins''" $ nf joins'' small
        ],
        bgroup "halfOverlapping" [
            bench "joins" $ nf joins halfOverlapping
          , bench "joins'" $ nf joins' halfOverlapping
          , bench "joins''" $ nf joins'' halfOverlapping
        ],
        bgroup "small" [
            bench "joins" $ nf joins small
          , bench "joins'" $ nf joins' small
          , bench "joins''" $ nf joins'' small
        ]
      ]
    ]
  ]

return []
-- | Run all @prop_@ tests
runTests :: IO Bool
runTests = $quickCheckAll

