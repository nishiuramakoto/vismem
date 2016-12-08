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
        pp x = text "(*)"

instance Pretty a =>  Pretty (Interval a) where
        pp (Interval.OpenInterval x y) = parens $ pp x <> comma <>  pp y

instance (HyperNum a, Eq s, Pretty a, Pretty s) => Pretty (Section a s) where
        pp = pp_section


pp_section :: (HyperNum a, Pretty a, Eq s, Pretty s) => Section a s -> Doc
pp_section s = text "Section" $$ nest 5 (pp_section_body (section_canonicalize s))

pp_section_body :: (HyperNum a, Pretty a, Eq s, Pretty s) =>  Section a s -> Doc
pp_section_body s =
        let gs = section_to_asc_list s
        in  vcat (map pp_section_gen gs)

pp_section_gen :: (HyperNum a, Pretty a, Eq s, Pretty s) => (Generator a, s) -> Doc
pp_section_gen (g,x) = pp g <+> text "->" <+> pp x
