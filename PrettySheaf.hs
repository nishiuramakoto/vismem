module PrettySheaf
       where

import Pretty
import Hyper
import Sheaf

import           Data.Map (Map, (!))
import qualified Data.Map as Map
import           Data.IntervalMap          (IntervalMap)
import qualified Data.IntervalMap          as IntervalMap
import           Data.IntervalMap.Interval (Interval)
import qualified Data.IntervalMap.Interval as Interval
-- for pretty printing without ghc extension
import qualified Data.IntervalMap.Generic.Strict as StrictIntervalMap

instance Pretty Singleton where
        pp_level n x = text "(*)"

instance Pretty a =>  Pretty (Interval a) where
        pp_level n (Interval.OpenInterval x y) = parens $ pp_level n x <> comma <>  pp_level n y

instance (HyperNum a, Eq s, Pretty a, Pretty s) => Pretty (Section a s) where
        pp_level n  = pp_section_summary n


pp_section_summary :: (HyperNum a, Pretty a, Eq s, Pretty s)
              => Hyper Integer -> Section a s -> Doc
pp_section_summary n s =
        case section_canonicalize s of
        Just s' -> text "Section" $$ nest 5 (pp_section_body_summary n s')
        Nothing -> text "Invlid Section" $$ nest 5 (pp_section_body_summary n s)


pp_section_body_summary :: (HyperNum a, Pretty a, Eq s, Pretty s)
                   =>  Hyper Integer -> Section a s -> Doc
pp_section_body_summary n s =
        let gs = section_to_asc_list s
        in  pp_list_summary n (map (pp_section_gen_summary n) gs)

pp_section_gen_summary :: (HyperNum a, Pretty a, Eq s, Pretty s)
                  => Hyper Integer -> (Generator a, s) -> Doc
pp_section_gen_summary n (g,x)
        = pp_level (n-1) g <+> text "->" <+> pp_level (n-1) x
