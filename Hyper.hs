{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
************************************************************************
*                                                                      *
*        A ring of hyperreals Q[dx,1/dx] and their intervals
*                                                                      *
************************************************************************

A model theoretical hack to make the tuple (a,b) really look like an 'open interval' yet cover
any closed/half-open finite/infinite intervals in a first-order definable total ordering.
For example:
* (a,b)     == hyper_std (a,b)
* [a,b]     == hyper_std (a-dx , b+dx)
* (-inf, a] == hyper_std (-1/dx, a+dx)
where hyper_std is the (continuous) projection onto the standard part.

This is useful e.g. as a base ring of coherent constructive Grothendieck topoi, see Sheaf.hs.
Another use would be to generalize the first order theory of lists, which we might call 'HyperList's.
(a 'Monad' in Haskell seems rarely monadic in this regard.)

For example, one might model strings as a HyperList where two consecutive chars are 'infinitely close',
and byte strings with two consective chars  'infinitely infinitely close' etc., realized as sheaves on
suitable Grothendieck topology.

Note that
1. induction (a kind of second order arithmetic) does not generalize automatically,
2. a multiple application of the hyperreal functor results in another perfectly
   valid (first order) theory of hyperreals.

@tbd: this should really work for any first-order definable total ordering, not just
      the numbers.

-}

module Hyper (
        -- * The class
        HyperNum(..),

        -- * The data type and its methods
        -- _unsafe functions are for reflection services
        Hyper(..),
        hyper_from_integral,
        hyper_std,
        hyper_d,
        hyper_inf,
        hyper_from_std,
        hyper_degree,
        hyper_floor,
        hyper_ceiling,

        -- * First order arithmetic theories
        -- ** Interval arithmetic
        hyper_interval_empty,
        hyper_interval_null,
        hyper_interval_intersection,
        hyper_interval_disjoint,
        hyper_interval_union,

        -- ** Action of hyper integers
        HyperSet(..),

        -- ** List (free monoid) arithmetic
        hyper_take,

        -- * Specifications
        spec_hyper_compare
        )
       where

import Invariant

import Data.Bits
import Data.List

import Text.Printf

import GHC.Generics (Generic)
import Control.DeepSeq

import Test.Hspec
import Test.QuickCheck
import Test.HUnit




class (Num a, Eq a, Ord a) => HyperNum a where
        dx  :: a -- ^ an arbitrary infinitesimal
        inf :: a -- ^ 1/dx

data Hyper a = HyperUnsafe
               { hyper_inv_dx_unsafe :: [a] -- ^ Infinites
               , hyper_std_unsafe    :: !a  -- ^ Standard part
               , hyper_dx_unsafe     :: [a] -- ^ Infinitesimals
               }
              deriving(Eq,Show, Generic, NFData)

instance (Num a, Eq a, Ord a) => HyperNum (Hyper a) where
        dx  = HyperUnsafe [] 0 [1]
        inf = HyperUnsafe [1] 0 []


instance Functor Hyper where
        fmap f (HyperUnsafe o x e) = HyperUnsafe (fmap f o) (f x) (fmap f e)

instance (Eq a, Ord a, Num a) => Ord (Hyper a) where
        compare = hyper_compare
        -- This is inefficient
        --h <= h' = hyper_leading_coefficient (h - h') <= 0

-- a bit of optimization
hyper_compare :: (Eq a, Ord a, Num a) => Hyper a -> Hyper a -> Ordering
hyper_compare (HyperUnsafe [] x []) (HyperUnsafe [] x' []) = compare x x'
hyper_compare (HyperUnsafe [] x (e:_)) (HyperUnsafe [] x' (e':_))
        | x /= x'   = compare x x'
        | e /= e'   = compare e e'

hyper_compare h h' = compare c 0
        where
                c = hyper_leading_coefficient (h - h')

spec_hyper_compare =
        it "compares two hypernumbers" $ do
                hyper_compare 0 0 @=? EQ
                hyper_compare dx 1 @=? LT
                hyper_compare (-dx) (-1) @=? GT
                hyper_compare (-dx) (-dx^2) @=? LT
                hyper_compare inf (inf-dx) @=? GT
                hyper_compare (inf^2) (inf+100) @=? GT
                hyper_compare (-inf^2) (inf+100) @=? LT

instance (Eq a, Ord a, Num a) => Num (Hyper a) where
        (*) = hyper_mult
        (+) = hyper_add
        negate (HyperUnsafe os x es)  = HyperUnsafe (map negate os) (negate x) (map negate es)
        fromInteger x           = HyperUnsafe [] (fromInteger x) []
        abs h                   = if h > 0 then h else -h
        signum h                = if h > 0 then 1 else if h == 0 then 0 else -1

instance (Num a, Bits a) => Bits (Hyper a) where
        h `shiftL` n = hyper_canonicalize $ fmap (`shiftL` n) h
        h `shiftR` n = hyper_canonicalize $ fmap (`shiftR` n) h
        (.&.) = undefined
        (.|.) = undefined
        complement = undefined
        rotate = undefined
        bitSize = undefined
        bitSizeMaybe = undefined
        isSigned = undefined
        testBit = undefined
        bit = undefined
        popCount = undefined
        xor = undefined

hyper_std :: Hyper a -> a
hyper_std = hyper_std_unsafe

hyper_from_integral :: (Integral a, Num b) => Hyper a -> Hyper b
hyper_from_integral x = fmap fromIntegral x


hyper_d :: Num a => Hyper a -> Hyper a
hyper_d (HyperUnsafe os x es) = HyperUnsafe [] 0 es

hyper_inf :: Num a => Hyper a -> Hyper a
hyper_inf (HyperUnsafe os x es) = HyperUnsafe os 0 []

hyper_from_std :: a -> Hyper a
hyper_from_std x = HyperUnsafe [] x []


hyper_degree :: (Eq a, Num a) => Hyper a -> Integer
hyper_degree (HyperUnsafe os x es) =
        let os_rev = dropWhile (==0) $ reverse os
            es_rev = dropWhile (==0) $ reverse es
        in
                case (null os_rev, x == 0, null es_rev) of
                (False, _, _)         -> fromIntegral $ length os_rev
                (True , False, _)     -> 0
                (True , True , False) -> fromIntegral $ length es_rev
                (True , True , True)  -> 0

-- | Compute the maximum hyper integer y s.t. y <= x @tbd generalize
hyper_floor :: Hyper Integer  -> Hyper Integer
hyper_floor x
        | hyper_d x >= 0 = x - hyper_d x
        | otherwise      = x - hyper_d x - 1

-- | Compute the minimum hyper integer y s.t. y >= x @tbd generalize
hyper_ceiling :: Hyper Integer  -> Hyper Integer
hyper_ceiling x
        | hyper_d x >  0 = x - hyper_d x + 1
        | otherwise      = x - hyper_d x


type HyperMonomial a = (a, Integer)

hyper_monomial_mult :: Num a => HyperMonomial a -> HyperMonomial a -> HyperMonomial a
hyper_monomial_mult (coeff, deg) (coeff', deg') = (coeff*coeff', deg + deg')

hyper_from_monomials :: (Num a, Ord a) => [HyperMonomial a] -> Hyper a
hyper_from_monomials ms = foldl' (+) 0 (map hyper_from_monomial ms)

hyper_from_monomial :: (Num a) => HyperMonomial a -> Hyper a
hyper_from_monomial (coeff, deg)
        | deg >  0  = HyperUnsafe (reverse (coeff : zeros (deg -1))) 0 []
        | deg == 0  = hyper_from_std coeff
        | deg <  0  = HyperUnsafe [] 0 (reverse (coeff : zeros (-deg-1)))
        where
                zeros n = take (fromIntegral n) $ repeat 0

hyper_monomials :: Hyper a -> [HyperMonomial a]
hyper_monomials (HyperUnsafe os x es) = zip os [1,2..] ++ [(x,0)] ++ zip es [-1,-2..]

hyper_mult h h'  = let ms  = hyper_monomials h
                       ms' = hyper_monomials h'
                   in hyper_from_monomials $ [hyper_monomial_mult m m' | m <- ms , m' <- ms' ]

hyper_add :: (Eq a, Num a) => Hyper a -> Hyper a -> Hyper a
hyper_add (HyperUnsafe os  x  es)  (HyperUnsafe os' x' es') =
        hyper_canonicalize $ HyperUnsafe (list_add os os') (x+x') (list_add es es')


hyper_leading_coefficient :: (Eq a, Num a) => Hyper a -> a
hyper_leading_coefficient (HyperUnsafe os x es)
        | any (/=0) os  = last_non_zero os
        | x /= 0        = x
        | any (/=0) es  = first_non_zero es
        | otherwise     = 0

hyper_canonicalize :: (Eq a, Num a) => Hyper a -> Hyper a
hyper_canonicalize (HyperUnsafe os x es) = HyperUnsafe os' x es'
        where
                os' = strip_right_if (==0) os
                es' = strip_right_if (==0) es

strip_right_if :: (a -> Bool) -> [a] -> [a]
strip_right_if p  = reverse . dropWhile p . reverse

first_non_zero :: (Num a, Eq a) => [a] -> a
first_non_zero    = head . dropWhile (==0)

last_non_zero :: (Num a, Eq a) => [a] -> a
last_non_zero     = first_non_zero . reverse

list_add xs ys
        | length xs > length ys = zipWith(+) xs (ys ++ repeat 0)
        | otherwise             = zipWith(+) (xs ++ repeat 0) ys


-- * Arithmetic theories
-- Any first order consistent theory on the base ring can be lifted to hyperreals

-- **  Hyper open interval arithmetics
-- It is important to include empty intervals to define Grothendieck topologies.
--

hyper_interval_empty :: HyperNum a => (a,a)
hyper_interval_empty = (0,0)

-- | The open interval (x,x) is empty
hyper_interval_null :: HyperNum a => (a, a) -> Bool
hyper_interval_null (a,b) = a >= b

hyper_interval_intersection :: HyperNum a
                               => (a, a)  -> (a, a) -> (a, a)
hyper_interval_intersection i@(ix,iy) j@(jx,jy) = (max ix jx, min iy jy)

hyper_interval_disjoint :: HyperNum a
                           => (a, a) -> (a, a) -> Bool
hyper_interval_disjoint i j = hyper_interval_null $ hyper_interval_intersection i j

hyper_interval_union :: HyperNum a
                        => (a, a) -> (a, a) -> [(a, a)]
hyper_interval_union i@(ix,iy) j@(jx,jy)
        | hyper_interval_disjoint i j = filter (not . hyper_interval_null) [i,j]
        | otherwise                   = [(min ix jx, max iy jy)]

-- |A large enough (but not maximal) compliment that covers the standard compliment
--  of even closed interval when projected
hyper_interval_large_complement :: HyperNum a
                                   => (a, a) -> [(a, a)]
hyper_interval_large_complement (a,b) = [(a - inf,  a-dx) , (b + dx, b + inf)]

-- | Same
hyper_interval_large_diff :: HyperNum a
                             => (a, a) -> (a, a) -> [(a, a)]
hyper_interval_large_diff i j =
        let [i1,i2] = hyper_interval_large_complement i
        in  (i1 /\ j) \/ (i2 /\ j)
        where
                (/\) = hyper_interval_intersection
                (\/) = hyper_interval_union



-- ** Action of hyper integers
-- Should satisfy the obvious laws

class HyperSet a where
        hyper_act_left  :: Hyper Integer -> a -> a
        hyper_act_left = flip hyper_act_right
        hyper_act_right :: a -> Hyper Integer -> a
        hyper_act_right = flip hyper_act_left


instance (HyperSet a, HyperSet b) =>  HyperSet (a,b) where
        hyper_act_left  g (a,b) = (hyper_act_left  g a, hyper_act_left  g b)
        hyper_act_right (a,b) g = (hyper_act_right a g, hyper_act_right b g)

instance (Num a, Ord a, Eq a) => HyperSet (Hyper a) where
        hyper_act_left x i = hyper_from_integral x + i



-- ** List arithemetic

hyper_take :: Hyper Integer -> [s] -> [s]
hyper_take n xs
        | n < 0           = error ("hyper_take negative:" ++ show n)
        | hyper_inf n > 0 = xs
        | otherwise       = take (fromIntegral $ hyper_std $ hyper_floor n) xs
