module Sheaf
where
import Pretty
import Hyper
import Invariant

import           Data.Map (Map, (!))
import qualified Data.Map as Map
import           Data.IntervalMap          (IntervalMap)
import qualified Data.IntervalMap          as IntervalMap
import           Data.IntervalMap.Interval (Interval)
import qualified Data.IntervalMap.Interval as Interval
-- for pretty printing without ghc extension
import qualified Data.IntervalMap.Generic.Strict as StrictIntervalMap

{-
************************************************************************
*                                                                      *
*        Sheaves
*                                                                      *
************************************************************************

 @FIXME: 1. For now only the trivial fibration is implemented.

 The goal is to unify and generalize Maps, Sets, IntervalMaps, etc.,etc..
 Examples include the time series of Sets/Maps, Maps over computable sets, and
 of cource "the time series of trees of virtual address spaces" as in our example program.
 With sheaves it should even be possible to model processes with shared memory,
 processes on NUMA systems, distributed systems, or anything you can even (computably) dream of.
 Sheaves also generalize monads, but probably not in Haskelly way.

 Reference: Sheaves in Geometry and Logic, S.MacLane, I.Moerdijk

For utmost concreteness we will progressively advance from the simplest to the more complex.

First, set A = Q[dx,1/dx], taking some fixed infinitesimal dx -- see Hyper.hs.
A is a hyper-real ring and is totally ordered.
It's not local, as each ideal (dx-a) == (1/dx-1/a) for which a/=0 is maximal.

Our first category OA:

objects  : *finite* unions of open intervals in A, including the empty set.
morphisms: inclusion as sets.

The fibered product A * B over X (i.e. the pullback of (A -> X <- B))
is the intersection A /\ B, which is also an object in OA.

Note that it's not complete nor cocomplete, and it's not topology in
ordinary sense.

Define a covering family of X to be a finite collection {X_i} of objects for which \/{X_i} == X.

This forms a Grothendieck pretopology. For, we have:
1. Fibered products exist.
2. Stability: Y -> X and X == \/{X_i} implies Y == \/{Y /\ X_i}.
3. Locality: X == \/{X_i} and X_i == \/{X_i_j} then X == \/{X_i_j}.
4. Isomorphisms: X == Y is a covering family.

The point is, we are freed from the insane uncomputablity of
the canonical topology! Now every 'open' set can be described by finite data
without losing any rigor. Thanks Grothendieck!

Now the sheaves. Fix some value-type V.

A sheaf F on OA is a contravariant functor OA^op -> V such that
for each covering family \/X_i == X, the diagram
F(X) -> ΠF(X_i) => ΠF(X_i /\ X_j)
of restictions is an equalizer.

Let's be concrete:

Let X   = X1 \/ X2
    X12 = X1 /\ X2 = X21
    0   = empty

    0                 |                  F(0)
    |      inclusion  | restriction       |
   X12       |        |     ^           F(X12)
    /\       |        |     |            /   \
  X1  X2     |        |     |         F(X1)  F(X2)
    \/       v        |     |           \     /
    X                 |                  F(X)

Both diagrams commute.

If V were a set with equality,

r1 :: F(X) -> F(X1)
r1 = F(X1 -> X)

r2 :: F(X) -> F(X2)
r2 = F(X2 -> X)

r12 :: F(X1) -> F(X12)
r12 = F(X12 -> X1)

r21 :: F(X2) -> F(X21)
r21 = F(X21 -> X2)

f :: F(X) -> (F(X1),F(X2))
f x = (r1 x, r2 x)

f1 :: (F(X1),F(X2)) ->  (F(X1), F(X12), F(X21), F(X2))
f1 (x,y) = (x, r12 x, r21 y, y)

f2 :: (F(X1),F(X2)) ->  (F(X1), F(X12), F(X21), F(X2))
f2 (x,y) = (x, r21 y, r12 x, y)

(f1 . f) x == (r1 x, r12 (r1 x), r21 (r2 x), r2 x)
(f2 . f) x == (r1 x, r21 (r2 x), r12 (r1 x), r2 x)

That f is an equalizer of f1 and f2 implies that the tuple (r1 :: F(X) -> F(X1) ,r2 :: F(X) -> F(X2))
can be determined by (r12 :: F(X1) -> F(X12)) and (r21 :: F(X2) -> F(X12)) in essentially unique way.
Although this says nothing about computability, is seems to reasonable to assume here that we have:

section_restrict_basis :: (OAB, v) -> OAB -> v
section_glue_basis     :: (OAB, v) -> (OAB, v) ->


Thanks to finiteness, we can describe a section of the sheaf by a *minimum* number of
pairs {(o_i,x_i)} s.t. o_i is an interval and o_i /\ o_j == 0 for i/=j. Such representation is unique
up to ordering. We call such a list of pairs the canonical covering of a section.

The category COA:
objects:   finite unions of half-open intervals [a,b)
morphisms: set inclusion

Let P be the power series functor PX = 1 + X + X^2 + X^3..
and let A* = PA.

-}

type A     = Hyper Integer
type Basis = HyperOpenInterval


data Section v = Section
                 { section_data     :: IntervalMap A v
                 }
               deriving (Show)

-- | O(log(n) * m) in average, O(n*m) at worst
section_glue :: Section v -> Section v -> Maybe (Section v)
section_glue x y = maybe_invariant "section_glue" precondition postcondition z
        where
                precondition    = section_valid x && section_valid y
                postcondition z = section_valid z

                z = foldl' glue x (section_bases y)

                glue x (i,v) = let (x0, x_rest) = section_split_bases i x
                               in  section_glue_bases (glue_slow x0 (i,v)) x_rest

                glue_slow x (i,v) = [ sheaf_glue (i,v) (j,u)
                                    | (j,u) <- section_covering x]


section_restrict :: (Eq v, Default v) => Section v -> Section v -> Section v
section_restrict x y = with_invariant "section_restrict" precondition postcondition z
        where
                precondition    = section_valid x && section_valid y
                postcondition z = section_valid z

                z = map (restrict x) (section_bases y)

                restrict x (i,v) = let x0 = section_component i x
                                   in  restrict_slow x0 (i,v)

                restrict_slow x (i,v) = [ sheaf_restrict (i,v) (j,u)
                                        | (j,u) <- section_bases x]



-- |Algebra of sections of sheaves, nullary operation. O(n)
-- Set the values on each open interval k to be (f k).
lift_section0 :: v -> Section v -> Section v
lift_section0 v a = with_invariant "lift_sheaf0"
                     precondition
                     postcondition
                     $ IntervalMap.map f a
        where
                precondition     = all disjoint_interval_tree [a] -- @FIXME: sheaf_valid
                postcondition vm = disjoint_interval_tree vm      -- @FIXME: sheaf_valid

-- | Unary operation. O(n)
lift_section1 :: (v -> v) -> Section v -> Section v
lift_section1 f a  = with_invariant "lift_sheaf1"
                   precondition
                   postcondition
                   $ IntervalMap.map f a
        where
                precondition     = all disjoint_interval_tree [a] -- @FIXME: coherency
                postcondition vm = disjoint_interval_tree vm      -- @FIXME: coherency


-- | Binary operation. O(n*m)
lift_sheaf2 :: (v -> v -> v) -> IntervalMap k v -> IntervalMap k v -> IntervalMap k v
lift_sheaf2 (*) a b = with_invariant "lift_sheaf2"
                      precondition
                      postcondition
                      $ union $ map (intersect a) (IntervalMap.toList b) -- @FIXME: slow
        where
                precondition      = all disjoint_interval_tree [a,b]
                postcondition vm  = disjoint_interval_tree vm

                intersect a (k,v) = let (lower, intersecting, upper) = IntervalMap.splitIntersecting a k
                                    in  intersect_slow intersecting (k,v)

                intersect_slow a (k,v) = let as = IntervalMap.toList a
                                         in  [ intersect_each (l,u) (k,v) | (l,u) <- as ]

                intersect_each (l,u) (k,v) =
                        case colim [l, k] of
                        Just lk -> (lk, u*v)
                        Nothing -> error "impossible"

                union xss = IntervalMap.fromList $ concat xss
