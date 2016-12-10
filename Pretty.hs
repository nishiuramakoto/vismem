-- |Rule of the game: never require fancy extensions
module Pretty(
        Pretty(..),
        Hex,
        Monomial,
        report,
        report_full,
        monomials,
        pp_error,
        pp_list,
        pp_list_summary,
        pp_tuple,
        pp_data,
        pp_timestamp,
        pp_polynomial,
        pp_monomial,
        module Text.PrettyPrint,
        module Text.Printf
        )
       where

import Numeric
import Hyper
import Data.Map(Map)
import qualified Data.Map as Map

import Text.PrettyPrint
import Text.Printf


class Pretty a where
        pp_level :: Hyper Integer -> a -> Doc

        pp         :: a -> Doc
        pp         = pp_level inf
        pp_summary :: a -> Doc
        pp_summary = pp_level 10
        pp_brief   :: a -> Doc
        pp_brief   = pp_level 5

-- |Report a summary of the data
report :: Pretty a => String -> a -> String
report desc d = render $
                text "REPORT<" <> text desc <> text ">" $$
                nest 2 (pp_summary d) $$
                text "END_REPORT\n"

-- |Report  data
report_full :: Pretty a => String -> a -> String
report_full desc d = render $
                     text "FULL_REPORT<" <> text desc <> text ">"  $$
                     nest 2 (pp d) $$
                     text "END_FULL_REPORT\n"

-- | Pretty error reporting
pp_error :: Doc -> a
pp_error = error . render


instance Pretty Doc     where pp_level _ = id
instance Pretty Int     where pp_level _ = text . show
instance Pretty Integer where pp_level _ = text . show
instance Pretty Bool    where pp_level _ = text . show

instance (Pretty a, Pretty b) => Pretty(a,b) where
        pp_level n  (a,b) = pp_tuple [ pp_level (n-1) a
                                     , pp_level (n-1)  b]

instance (Pretty a, Pretty b, Pretty c) => Pretty(a,b,c) where
        pp_level n (a,b,c) = pp_tuple [ pp_level (n-1) a
                                      , pp_level (n-1) b
                                      , pp_level (n-1) c]

instance (Pretty a, Pretty b, Pretty c, Pretty d) => Pretty(a,b,c,d) where
        pp_level n (a,b,c,d) = pp_tuple [ pp_level (n-1) a
                                        , pp_level (n-1) b
                                        , pp_level (n-1) c
                                        , pp_level (n-1) d]

instance Pretty a => Pretty [a] where
        pp_level   = pp_list_summary

pp_list_summary :: Pretty a => Hyper Integer -> [a] -> Doc
pp_list_summary n xs
        | len < n    = pp_list . map (pp_level (n-1)) $ xs
        | otherwise  = pp_list . add_ellipsis . map (pp_level (n-1)) . hyper_take n $ xs
        where
                add_ellipsis ps = ps ++ [text "..."]
                len = fromIntegral $ length xs

instance (Pretty k, Pretty v) => Pretty (Map k v) where
        pp_level n m = text "Map.fromList" <+> pp_level n (Map.toAscList m)


newtype Hex a = Hex a
instance (Integral a, Show a) => Show   (Hex a) where
        show (Hex x) =  sign x ++ "0x" ++ showHex (abs x) ""
                        where sign x | x >= 0    = ""
                                     | otherwise = "-"

instance (Integral a, Show a) => Pretty (Hex a)  where pp_level n = text . show

instance (Pretty a) => Pretty (Maybe a) where
        pp_level n (Just x) = text "Just" <+> pp_level n x
        pp_level n  Nothing = text "Nothing"



pp_list :: [Doc] -> Doc
pp_list = brackets . cat . punctuate comma

pp_tuple :: [Doc] -> Doc
pp_tuple = parens . cat . punctuate comma

pp_data :: String -> [(String, Doc)] -> Doc
pp_data constr body = text constr <+> braces (cat $ punctuate comma $ map field body)
        where
                field (name, doc) = text name <+> text "=" <+> doc

pp_timestamp = integer




-- Primitive polynomial support

type Monomial a = (a, String, Integer)

monomials x cs = zip3 cs (repeat x) [0..]
monomial_null (c,x,d) = c == 0

pp_polynomial :: (Show a, Num a, Ord a, Eq a) => [Monomial a] -> Doc
pp_polynomial = pp_polynomial' . filter (not . monomial_null)
        where
                pp_polynomial' [] = int 0
                pp_polynomial' (m:ms) = pp_monomial m <> cat (map pp_monomial_sign ms)

pp_monomial :: (Show a, Eq a, Ord a, Num a) =>  Monomial a -> Doc
pp_monomial (coeff,x,deg)
        | coeff == 0  = int 0
        | deg   == 0  = text (show coeff)
        | otherwise   = c <> var <> pow
        where
                c | coeff == 1  = empty
                  | coeff == -1 = text "-"
                  | otherwise   = text (show coeff)
                var = text x
                pow | deg == 0  = empty
                    | deg == 1  = empty
                    | otherwise = text "^" <> text (show deg)

pp_monomial_sign :: (Show a, Eq a, Num a, Ord a) => Monomial a -> Doc
pp_monomial_sign m@(coeff, x, deg)
        | coeff > 0 = text "+" <> pp_monomial m
        | otherwise = pp_monomial m

-- | Hyperreals

instance (Eq a, Ord a, Num a, Show a, Pretty a) => Pretty (Hyper a) where
        pp_level n (HyperUnsafe is x es) = pp_polynomial (infs ++ dxs)
                where
                        infs = reverse (monomials "inf" (x:is))
                        dxs  = tail    (monomials "dx" (0:es))

pp_hyper_interval :: (Eq a, Ord a, Num a, Show a, Pretty a) => (Hyper a, Hyper a) -> Doc
pp_hyper_interval (x,y) = parens $ pp x <> comma <>  pp y
