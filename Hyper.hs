{- |
************************************************************************
*                                                                      *
*        A ring of hyperreals Q[dx,1/dx] and its intervals
*                                                                      *
************************************************************************

A model theoretical hack to make the tuple (a,b) really look like an 'open interval' yet cover
any closed/half-open finite/infinite intervals in a first-order definable total ordering.
For example:
* (a,b)     == hyper_std (a,b)
* [a,b]     == hyper_std (a-dx , b+dx)
* (-inf, a] == hyper_std (-1/dx, a+dx)
where hyper_std is the (continuous) projection onto the standard part.

This is useful for e.g. defining coherent constructive Grothendieck topoi, see Sheaf.hs.

@tbd: this should really work for any first-order definable total ordering, not just
      the numbers.

-}

module Hyper (
        -- * The class
        HyperNum(..),

        -- * The data type and its methods
        Hyper,
        hyper_from_integral,
        hyper_std,
        hyper_d,
        hyper_inf,
        hyper_from_std,
        hyper_degree,

        -- * Interval arithmetic
        hyper_interval_empty,
        hyper_interval_null,
        hyper_interval_intersection,
        hyper_interval_disjoint,
        hyper_interval_union,

        -- * Action of hyper integers
        HyperSet(..),

        -- * Pretty printer
        pp_hyper_interval
        )
       where

import Invariant
import Pretty

import Data.Bits
import Data.List

import Text.Printf



class (Num a, Eq a, Ord a) => HyperNum a where
        dx  :: a -- ^ an arbitrary infinitesimal
        inf :: a -- ^ 1/dx

data Hyper a = Hyper { hyper_inv_dx :: [a] -- ^ Infinites
                     , hyper_std    :: a   -- ^ Standard part
                     , hyper_dx     :: [a] -- ^ Infinitesimals
                     }
              deriving(Eq,Show)

instance (Num a, Eq a, Ord a) => HyperNum (Hyper a) where
        dx  = Hyper [] 0 [1]
        inf = Hyper [1] 0 []


instance Functor Hyper where
        fmap f (Hyper o x e) = Hyper (fmap f o) (f x) (fmap f e)

instance (Eq a, Ord a, Num a) => Ord (Hyper a) where
        h <= h' = hyper_leading_coefficient (h - h') <= 0

instance (Eq a, Ord a, Num a) => Num (Hyper a) where
        (*) = hyper_mult
        (+) = hyper_add
        negate (Hyper os x es)  = Hyper (map negate os) (negate x) (map negate es)
        fromInteger x           = Hyper [] (fromInteger x) []
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


hyper_from_integral :: (Integral a, Num b) => Hyper a -> Hyper b
hyper_from_integral x = fmap fromIntegral x


hyper_d :: Num a => Hyper a -> Hyper a
hyper_d (Hyper os x es) = Hyper [] 0 es

hyper_inf :: Num a => Hyper a -> Hyper a
hyper_inf (Hyper os x es) = Hyper os 0 []

hyper_from_std :: a -> Hyper a
hyper_from_std x = Hyper [] x []


hyper_degree :: (Eq a, Num a) => Hyper a -> Integer
hyper_degree (Hyper os x es) =
        let os_rev = dropWhile (==0) $ reverse os
            es_rev = dropWhile (==0) $ reverse es
        in
                case (null os_rev, x == 0, null es_rev) of
                (False, _, _)         -> fromIntegral $ length os_rev
                (True , False, _)     -> 0
                (True , True , False) -> fromIntegral $ length es_rev
                (True , True , True)  -> 0

type HyperMonomial a = (a, Integer)

hyper_monomial_mult :: Num a => HyperMonomial a -> HyperMonomial a -> HyperMonomial a
hyper_monomial_mult (coeff, deg) (coeff', deg') = (coeff*coeff', deg + deg')

hyper_from_monomials :: (Num a, Ord a) => [HyperMonomial a] -> Hyper a
hyper_from_monomials ms = foldl' (+) 0 (map hyper_from_monomial ms)

hyper_from_monomial :: (Num a) => HyperMonomial a -> Hyper a
hyper_from_monomial (coeff, deg)
        | deg >  0  = Hyper (reverse (coeff : zeros (deg -1))) 0 []
        | deg == 0  = hyper_from_std coeff
        | deg <  0  = Hyper [] 0 (reverse (coeff : zeros (-deg-1)))
        where
                zeros n = take (fromIntegral n) $ repeat 0

hyper_monomials :: Hyper a -> [HyperMonomial a]
hyper_monomials (Hyper os x es) = zip os [1,2..] ++ [(x,0)] ++ zip es [-1,-2..]

hyper_mult h h'  = let ms  = hyper_monomials h
                       ms' = hyper_monomials h'
                   in hyper_from_monomials $ [hyper_monomial_mult m m' | m <- ms , m' <- ms' ]

hyper_add h h'   =
        let Hyper os  x  es  = h
            Hyper os' x' es' = h'
        in
                hyper_canonicalize $ Hyper (list_add os os') (x+x') (list_add es es')







hyper_leading_coefficient :: (Eq a, Num a) => Hyper a -> a
hyper_leading_coefficient (Hyper os x es)
        | any (/=0) os  = last_non_zero os
        | x /= 0        = x
        | any (/=0) es  = first_non_zero es
        | otherwise     = 0

hyper_canonicalize :: (Eq a, Num a) => Hyper a -> Hyper a
hyper_canonicalize (Hyper os x es) = Hyper os' x es'
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


-- *  Hyper open interval arithmetics
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



-- * Action of hyper integers
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



-- * Pretty Printers
--
--

pp_hyper_interval :: (Eq a, Ord a, Num a, Show a, Pretty a) => (Hyper a, Hyper a) -> Doc
pp_hyper_interval (x,y) = parens $ pp x <> comma <>  pp y

instance (Eq a, Ord a, Num a, Show a, Pretty a) => Pretty (Hyper a) where
        pp (Hyper is x es) = pp_polynomial (infs ++ dxs)
                where
                        infs = reverse (monomials "inf" (x:is))
                        dxs  = tail    (monomials "dx" (0:es))
