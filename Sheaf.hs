{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
************************************************************************
*                                                                      *
*        Sheaves
*                                                                      *
************************************************************************

 One of the fascinating ideas in math is the study of
 deep algebraic/logical  structures under the light  of
 human geometric/topological intuition.

 The goal of this library is exactly this; it tries to 'geometrize' data structures
 (with the ultimate goal of 'geometric programming')  with the help of Topos Theory.

 We will try to unify and generalize Lists, Trees, Maps, Sets, IntervalMaps, Continuations, or
 any combination of them, etc.,etc.. in order to give them geometric studies.

 If some data structure could be pictorized on paper, chances are that its 'geometry'
 may be modeled by a sheaf on a site with a (often coherent) computable
 description of its Grothendieck topology.

 Examples include the time series of Sets/Maps, Maps over decidable
 sets (whose algebra, i.e. the boolean lattice of decidable sets,
 corresponds to a boolean continuation monad making it a  boolean topos),
 Maps over 'local ordering' patched together (e.g. the unit circle), and
 of cource "the time series of trees of virtual address spaces" as in
 our example program.

 With sheaves it will be possible to model processes with shared memory,
 processes on NUMA systems, distributed systems possibly equipped with 'eventual consistency',
 in a way that strongly reflects the  programmer's natural geometrical/topological intuition,
 without sacrificing  algebraic/logical rigor.

 Sheaves also generalize monads (or any 'geometric theory' -- see below), but
 probably not in Haskelly way (because categorical programming in Haskell
 seems a bit cranky and unnatural.. but I really don't know.)

= A note about computing constant sheaves on a constructive site

The purpose of this note is to explain how constant sheaves are
derived constructively from a computable description of a site.

Contents
0. Notation
1. An Example of a Constructive Site
2. Sheaves on a Site
3. The Associated Sheaf Functor
4. Constant Sheaves and Global Sections
5. Construction of Constant Sheaves
6. Examples of Constant Sheaves
7. Sections of Constant Sheaves
8. Geometric Morphisms between Constructive Grothendieck topoi
9. Geometric Theories

References:
[1] S.MacLane, I.Moerdijk, Sheaves in Geometry and Logic
[2] P.Johnstone, Sketches of an Elephant: A Topos theory Compendium


== 0. Notation

Because relative sizes of unicode characters are not standardized,
I will use ASCII characters exclusively where the correct
indentation matters.

Sets          = the category of sets
0             = the initial object
1             = the terminal object

f::X->Y       = a morphism from X to Y
Hom(X,Y)      = similar to X->Y, but emphasizes that it's a *set* of morphisms.

X /\ Y over Z = the fibered product of X and Y over Z for some implicit
                f::X->Z and g::Y->Z. I will omit 'over Z' where that doesn't seem
                to cause confusion.

[x]           = mostly an equivalence class, not a list.
{f x| x <- s, p x,..} =
   a hypothetical monadic comprehension defining a set, thout it need not be
   constructive. Note that the right-adjoint of the powerset functor is evidently monadic over Sets;
   its algebra is the complete boolean lattice.

Warnings:
Haskell functions will be written in underscore_case. This has several advantages:
1. Mathematical, non-constructive functions/morphisms are easily
   distinguished with constructive Haskell functions,
2. The well-tested standard library functions are clearly distinguished
   with our under-tested ones,
3. It looks more like my favarite languages like C/Ocaml/Prolog/etc than, say,... Java.

== 1. An Example of a Constructive Site

For utmost concreteness let us concentrate on a simplest possible case.

First, let A = Q[dx,1/dx], taking some fixed infinitesimal dx -- see Hyper.hs.
A is a hyper-real ring and is totally ordered.
It's not local, as each ideal (dx-a) == (1/dx-1/a) for which a/=0 is maximal.

Our first site (C,K):

objects  : finite unions of open intervals in A, including the empty set.
morphisms: inclusion as sets.

The fibered product A * B over X (i.e. the pullback of (A -> X <- B))
always exists as the intersection A /\ B (in X).

Note that it's neither complete nor cocomplete, and it's not topology
of A in ordinary sense.

For any X in C, there is a unique  finite set of
disjoint intervals X1..Xn s.t. X = X1 + X2 .. Xn.
Consider a set of 2^n combinations Kc(X) = {0, X1.., X1+X2,.. X1+X2..Xn}
and let  K(X) = {S in Kc(X) | ΣS = X}.

Now K forms a basis for a Grothendieck topology because:

1. The isomorphism X = ΣXn is in K(X).
2. Stability: if S ={C1..Ck}  in K(X), Y -> X, then {Ci/\Y over X} is in  K(Y).
3. Transitivity: if {Ci} in K(X) and {Dij} in K(Ci) then {Dij} is in K(X).

(Note that C is a full-subcategory of Zariski open sets in one dimension.)

So (C,K) is a site. It is of finite type since C has finite
limits and also K(X) is finite for any X. That is, the Grothendieck topos Sh(C,K) (i.e. the
category of sheaves on (C,K)) is a coherent topos.

The point is, we are now free from the insane uncomputablity  of
the classical topology! Now every 'open set' can be described by finitary data
without sacrificing rigor or topological intuition. Thanks Grothendieck!

On the other hand, the Lawvere-Tierney topology, being an operator
on the subobject classifier Ω, is again not directly computable
(in many of the interesting cases), even though
it agrees with the Grothendieck in the case of sheaves.

Of course, it will be worth checking if some constructive 'topology' of your
non-Grothendieck topos gives the same thing as the Lawvere-Tierney topology.

== 2. Sheaves on (C,K)

A sheaf F (for French 'faisceau') on a site (C,K) is a contravariant functor C^op -> Sets such that
for each covering family X = ΣX_i, the following diagram is an equalizer:

        e           p1
   F(X) -> ΠF(X_i) => ΠF(X_i /\ X_j)   -- (1)
                    p2

where
  /\ is the fibered product over X
  e = ∏F(X_i -> X)
  p1= ∏F(X_i /\ X_j -> X_i)
  p2= ∏F(X_i /\ X_j -> X_j)

Let's be concrete..

Let X   = X1 \/ X2
    X12 = X1 /\ X2 = X21
    0   = empty

               C      |   Sets
    0                 |                  F(0)
    |      inclusion  | restriction       |
   X12       |        |     ^           F(X12)
    /\       |        |     |            /   \
  X1  X2     |        |     |         F(X1)  F(X2)
    \/       v        |     |           \     /
    X                 |                  F(X)


Now the above equalizer just says that the diagram on the right is a
pullback, so that we have the following explicit description of F(X):

F(X) = {(x,y) | x <- F(X1), y <- F(X2), r12(x) == r21(y) }  --- (2)
where
   r12 = F(X12 -> X1)
   r21 = F(X12 -> X2)


On the other hand, it should be clear that there must be a unique
injection from the pushout P of (F(X1) <- F(X) -> F(X2)) to  F(X12):

     F(X12)      Sets
       .
       .        restriction
       P          ^
     /   \        |
  F(X1)  F(X2)    |
    \     /       |
     F(X)

where P = (F(X1) + F(X2))/~
      (+) = coproduct
      (~) = equivalence relation defined by r1(x) ~ r2(x)
      r1 = F(X1 -> X)
      r2 = F(X2 -> X)


That is, F(X12) may be arbitrarily large, with tons of non-extendable local objects.
However it must at least contain the pushout, namely the restrictions of the 'more global' objects.
When F(X12) is exactly such pushout for any X1 and X2, one often says F is flabby (French flasque).

(Flabby sheaves are probably so-called because their global sections (see below) are relatively abundant,
but one could also say they are 'lean' locally..)

Note that the structure of F(0) cannot be determined by this equalizer alone. You could, for example,
construct a sheaf where F(0) = {0,1,2}.
Consequently, it's not always true that F(X) = ∏F(X_i) even if X_i are all disjoint
(i.e. if all the fibered products are initial).

== 3. The Associated Sheaf Functor

Forgetting the equalizer, we get an inclusion from the category of
sheaves into the category of presheaves, denoted as 'i'. It is known
to have a left-adjoint 'a' which preserves finite limits([1], Theorem 1, III.5):

a:Psh(C) <--> Sh(C,K):i

where Psh(C) = C^op -> Sets.

This 'a' is called the associated sheaf functor, and applying 'a' is
said to be the 'sheafification'.

Proposition ([1], Corollary 6, III.5):
   a . i :: Sh(C,J) -> Sh(C,K)
   is naturally isomorphic to the identity functor.

Proof:
i, as the inclusion to Psh(C), is full and faithful.
(but of course a need not be faithful.)
Now the counit of an adjunction is an isomorphism iff
the right adjoint is full and faithful.
(end of proof)

The above adjunction implies, among other things, that any morphism
f from a presheaf P to a sheaf F (as a natural transformation of functors)
uniquely factors through a(P) (which is often identified as i(a(P))).
That is, there exists f~::a(P)->F making the following diagrams commute:

      η_P        in Psh(C)  |  for X -> Y in C:
    P ----> a(P)             |
    |      /                 |   PY ---> a(P)Y ---> FY    in Sets
    |     /                  |   |         |        |
  f |    / f~                |   |         |        |
    |   /                    |   |         |        |
    v  v                     |   v         v        v
    F                        |   PX ---> a(P)X ---> FX


The explicit construction of 'a' is a bit messy, involving the 'plus-construction' applied twice.
We will only consider the case of constant sheaves below.

Historically many of these machinaries have been invented for the sake of developing suitable
cohomology theories to study global invariants of a space.
A cohomology theory then is a functor from a category of some
geometric figures (e.g. schemes) to some algebraic category (abelian
category) in a way that reflects their topological 'shapes'.
Cohomology groups matter, for example, when some global phenomena on a figure
(e.g. running a circular track) affect the calculation of  data (e.g. track count).
Weibul[3] notes Riemann's remark about a special case of Stokes' Theorem as one such example.

Fortunately (or not), our site is simple enough that cohomology groups won't matter.
We just track, through sheaves, how local changes to a data structure propagate to the global state,
and in any case things like overflows or vanishing of integrals won't happen.

== 4. Constant Sheaves and Global Sections

Let S be a set.
The constant presheaf ΔS is the contravariant functor in Psh(C) s.t.
ΔS(X) = S and ΔS(X->Y) = id for all X,Y in C.

A constant sheaf (on a site (C,K)) is the sheafification a(ΔS) of
a constant presheaf ΔS, and also denoted ΔS when no confusion would arise.

Δ, considered as a functor from Sets to Sh(C,K), has a right adjoint Γ:

Δ:Sets <--> Sh(C,K):Γ

where Γ is the natural transformation Hom(Δ1,-), called the global
section functor.

The constant sheaves are actually our main data structure, so we shall calculate them explicitly.
Intuitively, it should be obvious, it's a sheaf of 'locally constant' functions discussed below.

== 5. Construction of Constant Sheaves

The goal of this section is to give an explicit, constructive description of constant sheaves
on arbitrary site. The simpler but non-constructive description
ΔS≃∐Δ1
    S
will not be of much use for our computing purposes.

WARNING:
  Careful, this is my own. You'll find mistakes!

Hereafter in this section, I write ΔS as the constant presheaf.

Let (C, K) a site. By (our) definition,
  1. C is small and has pullbacks and the initial object 0,
  2. K is a basis for a Grothendieck topology.

Let S be a set. Our first goal is to define a sheaf D(S), to be shown
isomorphic to the constant sheaf a(ΔS),  as follows:

  X             D(S)(X)  = colim(Hom(R, S))
  |                ^        R in KD(X)^op
 f|         D(S)f  |
  v                |
  X'            D(S)(X') = colim(Hom(R', S))
                            R' in KD(X')^op

Let's make sense of the above diagram.

First, KD(X) is a family of 'disjoint coverings' (sorry, my terminology) for X:

1. KD(X) = {R in K(X) | R is a disjoint covering for X },
2. R is a disjoint covering for X iff any two (c::U->X), (c'::U'->X) of R are disjoint in X,
3. (c::U->X), (c'::U'->X) are disjoint in X iff the following diagram is a pullback:

    0
   / \    |
  U   U'  |
  c\ /c'  v
    X

where 0 is the initial object.

KD satisfies the three axioms for a basis:
1. The isomorphism {X->X} is in KD(X),
2. Stability: if R is in KD(X) and f::Y->X then R /\ Y is in KD(Y)
   (where R /\ Y = {c /\ Y in X | c in R}),

        0
       / \         Proof:
     U*Y U'*Y      From the left diagram one concludes that there has to be unique (U*Y)*(U'*Y) -> 0.
      /\ /\        (writing (*) = (/\ over X))
      U Y U'
       \|/
        X


3. Transitivity: if R={Ci} in KD(X) and Ri={Dij} in KD(Ci) then {Dij} is in KD(X).

         0
        /  \
       /    \           Proof:
      Dij    Dkl        Similar to above, there has to be a unique Dij * Dkl -> 0 for i/=k.
      |      |
      Ci     Ck
       \    /
         X


For any X, KD(X) forms a (cofiltered) subcategory of Sets (since we assumed C to be small) as follows:

1. R in KD(X) is considered as a set of covers {U -> X},
2. A morphism h::Q->R is defined iff Q is a refinement of R,
   i.e. for R={Ui->X} in KD(X), Ri={Vij->Ui} in KD(Ui), Q={Vij->Ui->X}.
   Then for c::Vij->X in Q we can uniquely assign h(c)::Ui->X in R.
   (Here uniqueness follows from Vij/\Uk == 0 for i/=k.)
3. It's clearly cofiltered but we don't seem to use it, so proof is omitted.

Next, we observe that f::X->X' in C induces a natural transformation f*::KD(X)->KD(X'):

                              f*
          Q={g::U->V->X} ---------> Q'={f.g::U->V->X->X'}
            |                         |
            | h                       | h
            v                 f*      v
          R={h(g)::V->X} ---------> R'={h(f.g)::V->X->X'}

The well-definedness and the commutativity of this diagram immediately
follows from the properties of KD(X) above.

Thus we have the object D(S)X = colim(Hom(R,S)).
                                  R in KD(X)^op

As for D(S)(f::X->X'), the following diagram should be self-explanatory:

             h^(*)
Hom(R, S) ------------> Hom(Q, S)  --...--> colim(Hom(R,S))
  |                      |                     R in KD(X)^op
  |                      |                        |
  | f^(*)                | f^(*)                  | D(S)f
  v          h^(*)       v                        v
Hom(R', S) -----------> Hom(Q',S)  --...--> colim(Hom(R',S))
                                               R' in KD(X')^op

This completes the proof that D(S) is a presheaf.

Next we need to prove that D(S) is indeed a sheaf.
For this, we need to show the following digram is an equalizer:

D(S)(X) -> ΠD(S)(X_i) => Π(D(S)(X_i /\ X_j))

where {X_i -> X} is a covering in K(X).

As before we can visualize the essense of this equalizer by depicting the
corresponding pullback for the binary cover X=X1\/X2:

                       colim
                       --->
   Hom(0,S)              |      D(S)(0)
     |                   |        |
   Hom(R12,S)            |     D(S)(X12)
    /     \              |     /       \
Hom(R1,S)  Hom(R2,S)     | D(S)(X1)    D(S)(X2)
   \        /            |     \       /
   Hom(R,S)              |       D(S)X


where R={Ui->X} is a cover in KD(X),
      R1={Ui/\X1->X1},
      R2={Ui/\X2->X2},
      R12={Ui/\X12->X12}

From this D(S) is easily a sheaf (proof omitted).

Finally we note that there is a canonical presheaf morphism d::ΔS -> D(S):

d(X)::S -> colim(Hom(R,S))
             R in KD(X)^op
d(X)(x) = [\_ -> x]

where [f] denotes the equivalence class.


Now I claim D(S) == a(ΔS). Assuming the existence of the adjunction
a -| i, I need to show the following:

   for any sheaf F and presheaf morphism f:ΔS -> F, there exists a
   factorization f~, which is a sheaf morphism:

        f
    ΔS -> F
     |   ^
   d |  / f~
     v /
    D(S)

Then by the property of adjunctions (the universality of units)
it follows that D(S) = i(a(ΔS)).

But this is easy:

f~(X)::D(S)(X) -> F(X)
f~(X) ([g::Hom(R,S)]) = [{f(g(c::U->X)) | c in R}]

where [_] is the equivalence class, {_} is the matching family.

TODO: explain matching families.

== 6. Examples of Constant sheaves

A constant sheaf on a locally connected topological space is trivial:
a(ΔS)(X) = ΠS where the product is over the connected components of X.

For a slightly less trivial, yet computationally significant example,
consider the following site (C',K'):

objects:   finite unions of half-open intervals (a,b] in Q
morphisms: set inclusion
K(X) = the set of all finite coverings of X

This is not coherent, but constructive. We have:

a(ΔS)(X) = colim(Hom(R,S))
              R in KD(X)^op

          = the set of all step functions

== 7. Sections of Constant Sheaves

Hereafter ΔS will denote the constant sheaf again.

A section x on X of a sheaf F is an element x in F(X).

To emphasize concreteness, here I
concentrate on sections of constant sheaves on the site (C,K) given
in Section 1., in a way that could facilitate further generalizations.

objects  : finite unions of open intervals in A, including the empty set.
morphisms: inclusion as sets.
K(X) = the combinations of maximal disjoint intervals which cover X (as a set).

-}

module Sheaf
where

import Hyper
import Invariant

import Data.Maybe
import Data.List

import           Data.IntervalMap.Strict    (IntervalMap)
import qualified Data.IntervalMap.Strict   as IntervalMap
import           Data.IntervalMap.Interval (Interval)
import qualified Data.IntervalMap.Interval as Interval

import GHC.Generics (Generic)
import Control.DeepSeq
import Control.Exception

import Test.Hspec
import Test.QuickCheck
import Test.HUnit hiding(assert)

-- | The base ring
type A         = Hyper Integer

type Singleton = () -- ^ The terminal set (==1 in Sets)

{-|
Recall that a strong/effective/split generating family is a collection of objects {G_i} such that

e_X::∐G_i        -> X
     i,f::G_i->X

exists and is a strong/effective/split epimorphism for each X.

In our category (C,K), the set of disjoint intervals serves as the generating family in whatever sense,
because e_X is always the identity.
Furthermore, the domain of e_X is actually isomorphic to a finite coproduct of the generators,
although it's neither noetherian nor compact.

The trouble is that I can't recall a proper name for expressing such things..
so let us just call them 'generators', and the sections on them 'generating sections'.

In the sequel, I will add the suffix '_at' to the name of an operation of a section
that acts locally near the given generator, in order to emphasize that the objects of our generating family
is considered as generalized points.

As noted above, it is essential that our generating family contains open intervals only.
Otherwise its sections must necessarily include step functions with infinite number of jumps,
in which case the representation of sections as the finite map of intervals would not be sufficient.
-}

type Generator a    = OpenInterval a
type OpenInterval a = Interval a



-- For testing
type GenA = Generator A

-- induce algebras from the dst space
induce0 :: (a -> b) -> (c) -> (c -> d) -> d
induce0 from x0 to = to (x0)

induce1 :: (a -> b) -> (b -> c) -> (c -> d) -> a -> d
induce1 from f to = \x -> to (f (from x))

induce2 :: (a -> b) -> (b -> b -> c) -> (c -> d) -> a -> a -> d
induce2 from (*) to = \x y -> to (from x * from y)

-- | Gives a generator
gen :: HyperNum a => (a,a) -> Generator a
gen (x,y) = Interval.OpenInterval x y

-- For testing
genA :: (A,A) -> GenA
genA = gen

-- | Lower bound of an open interval
gen_lower_bound :: HyperNum a => Generator a -> a
gen_lower_bound = fst . from_gen

-- | Upper bound of an open interval
gen_upper_bound :: HyperNum a => Generator a -> a
gen_upper_bound = snd . from_gen


-- | Converts a generator to a tuple (since it resembles like an open interval)
from_gen :: HyperNum a => Generator a -> (a,a)
from_gen (Interval.OpenInterval x y) = (x,y)


-- | The initial object
gen_empty :: HyperNum a => Generator a
gen_empty = induce0
            id
            hyper_interval_empty
            gen

-- For testing
g0 = gen_empty :: GenA

-- spec_FUN is meant to serve as the specification and as the documentation of FUN, NOT as a test
-- Real tests should be done elsewhere
spec_gen_empty = it "specifies the initial object" $ do
       g0 @=? gen (0,0)

-- | Tests initiality
gen_null  :: HyperNum a => Generator a -> Bool
gen_null = induce1
           from_gen
           hyper_interval_null
           id

spec_gen_null = it "tests the initiality of a generator" $ do
        gen_null g0          @=? True
        gen_null (gen (0,1) :: GenA) @=? False


-- | Union (the coproduct) of two generators as a sorted list of generators (in asc order)
gen_unions :: HyperNum a => Generator a -> Generator a -> [Generator a]
gen_unions = induce2
             from_gen
             hyper_interval_union
             (sort . map gen)

spec_gen_unions = it "computes the union of two generators" $ do
        gen_unions g0 g0     @=? []
        gen_unions g0 (gen (1,2))   @=? [gen (1,2)]
        gen_unions (genA (1,2)) (genA (2,3)) @=? [genA (1,2), genA (2,3) ]
        gen_unions (genA (1,2)) (genA (2-dx,3)) @=? [genA (1,3)]

-- partial, dangerous
gen_union  :: HyperNum a => Generator a -> Generator a -> Generator a
gen_union  = induce2
             from_gen
             hyper_interval_union
             (head . map gen)

spec_gen_union = it "partially computes the union of two intersecting generators" $ do
        gen_union (genA (1,2+dx)) (genA (2,3)) @=? genA (1,3)
        gen_union (genA (1,2))    (genA (0,1+dx)) @=? genA (0,2)

-- | The fibered product x∩y over x‌/y/x∪y (all the same on our site)
gen_intersection :: HyperNum a => Generator a -> Generator a -> Generator a
gen_intersection = induce2
                   from_gen
                   hyper_interval_intersection
                   gen

spec_gen_intersection = it "computes the fibered product x∩y over x∪y" $ do
        gen_intersection (genA (1,2)) (genA (2,3))    `shouldSatisfy` gen_null
        gen_intersection (genA (1,2)) (genA (2-dx,3)) @=? genA (2-dx,2)
        flip gen_intersection (genA (1,2)) (genA (2-dx,3)) @=? genA (2-dx,2)

-- | Are x and y disjoint? i.e. Is x/\y initial?
gen_disjoint :: HyperNum a => Generator a -> Generator a -> Bool
gen_disjoint = induce2
               from_gen
               hyper_interval_disjoint
               id

spec_gen_disjoint = it "tests whether two generators are disjoint" $ do
        gen_disjoint g0 g0         @=? True
        gen_disjoint (genA (1,2)) g0    @=? True
        gen_disjoint (genA (1,2)) (genA (2,3))    @=? True
        gen_disjoint (genA (1,2)) (genA (2-dx,3)) @=? False
        flip gen_disjoint (genA (1,2)) (genA (2-dx,3)) @=? False

-- | Do x y intersect? That is, is x/\y non-intial?
gen_intersects :: HyperNum a => Generator a -> Generator a -> Bool
gen_intersects = induce2
                 from_gen
                 hyper_interval_disjoint
                 not

spec_gen_intersects = it "tests x∩y /= 0" $ do
        gen_intersects g0 g0         @=? False
        gen_intersects (genA (1,2)) g0    @=? False
        gen_intersects (genA (1,2)) (genA (2,3))    @=? False
        gen_intersects (genA (1,2)) (genA (2-dx,3)) @=? True
        flip gen_intersects (genA (1,2)) (genA (2-dx,3)) @=? True


{-|
Next we recall that

Δs(X) = colim(Hom(R,s))
          R in KD(X)^op

which is a set of equivalence classes represented by (f::R->s) for R
a disjoint covering {c::U->X}. Since on our site a disjoint
covering can always be described by a finite set, it is natural to
express the sections by some kind of finite maps.

WARNING:
Note that this is not possible in general. For, consider a sheaf of
computable functions totally defined on their domains. Then there exists a section
on a (bounded) interval which cannot be glued together by its finite number of computable restrictions.
That is, the choice of data structures necessary to represent the sections critically depends
on the base topology and on the type of the sheaf.
-}

-- @tbd: I could not find higher dimensional range trees in Hackage?? Will I have to do it?
data Section a s = SectionUnsafe
                 { section_genmap_unsafe   :: IntervalMap a s -- ^ Open intervals only
                 , section_gencount_unsafe :: ! Int           -- ^ IVMap doesn't keep size data???
                   -- , section_canonical :: ! Bool           -- ^ @tbd for efficiency
                 }
               deriving (Show, Generic, NFData)

-- Internal only
section_to_tuple_unsafe (SectionUnsafe map n) = (map,n)

-- Interval only
section_smaller_unsafe s t = section_gencount_unsafe s < section_gencount_unsafe t

-- Not well-defined on equivalece classes,
-- but the implication 'section_eq_unsafe --> (==)' does hold
section_eq_unsafe :: (HyperNum a, Eq s)
                     => Section a s -> Section a s -> Bool
section_eq_unsafe (SectionUnsafe map n) (SectionUnsafe map' n') =
        n == n' && map == map'


-- Change the representation to an interval map, doesn't check consistency
section_from_list_unsafe :: HyperNum a => [(Generator a, s)] -> Section a s
section_from_list_unsafe gs = foldl' (<*) section_empty gs
        where
                SectionUnsafe map n <* (g,x) = SectionUnsafe (IntervalMap.insert g x map) (force $ n+1)
                force x = x `seq` x

section_from_list_unsafe' :: HyperNum a => [(Generator a, s)] -> Section a s
section_from_list_unsafe' gs = SectionUnsafe map n
        where
                map = IntervalMap.fromList gs
                n   = length gs


-- Glueing without checking
-- O(m*log n) for smaller m
-- @tbd treat the case where m*log n > m + n
section_glue_unsafe :: HyperNum a => Section a s -> Section a s -> Section a s
section_glue_unsafe (SectionUnsafe m n) (SectionUnsafe m' n') =
        with_invariant "section_glue_unsafe"
        precondition
        postcondition
        $ SectionUnsafe m'' (n+n')
        where
                precondition    = n >= 0 && n' >= 0
                postcondition s = True

                m'' | n > n'    = m  <* m'
                    | otherwise = m' <* m

                m <*  m'     = IntervalMap.foldlWithKey insert m m'  -- No foldl' ??
                insert m g x = force $ IntervalMap.insert g x m
                force x      = x `seq` x

-- Not well-defined, internal only
section_foldl'_unsafe :: (t -> (Generator a, s) -> t) -> t -> Section a s -> t
section_foldl'_unsafe (*) x s = IntervalMap.foldlWithKey f x (section_genmap_unsafe s)
        where
                f x g v = force $ x * (g,v)
                force x = x `seq` x

-- Not well-defined, internal only
section_foldr_unsafe :: ((Generator a, s) -> t -> t) -> t -> Section a s -> t
section_foldr_unsafe (*) x s = IntervalMap.foldrWithKey f x (section_genmap_unsafe s)
        where
                f g v x  = (g, v) * x

-- | The domain of a section, represented as a list of generators in asc order
section_domain_asc :: HyperNum a => Section a s -> [Generator a]
section_domain_asc = map fst . section_to_asc_list


-- | Change the representation to a sorted list of generating sections
section_to_asc_list :: HyperNum a => Section a s -> [(Generator a, s)]
section_to_asc_list s = IntervalMap.toAscList $ section_genmap_unsafe s


-- | Tests wheter it is the (unique) section on the initial object, i.e. F(0).
--   Note that this is really a terminal object in the category of sections and restrictions..
--   What would be the better name of this?
section_null :: HyperNum a => Section a s -> Bool
section_null (SectionUnsafe m n) =
        with_invariant "section_null"
        precondition
        postcondition
        $ n == 0
        where
                precondition    = n >= 0
                postcondition b = b == IntervalMap.null m

spec_section_null = it "tests x == F(0) " $ do
        section_null s0  @=? True
        section_null (section_singleton (genA (0,1),1))   @=? False

-- | F(0), i.e. the unique section on the initial object
section_empty :: HyperNum a => Section a s
section_empty = SectionUnsafe IntervalMap.empty 0

-- To simplify testing
s0 = section_empty :: Section A Int

-- | The section on a single generator
section_singleton :: HyperNum a => (Generator a, s) -> Section a s
section_singleton (g,x) = SectionUnsafe (IntervalMap.singleton g x) 1

{-
The most basic building block for defining topological operations
to ensure reasonable computational complexity (e.g. O((log n)^d) for a dimension d).
Note that this itself is not a well-defined topological operation.

It splits the section into two parts: local generators and non-local generators.
The two may not necessarily be disjoint; so this doesn't topologically make sense.
-}
section_split_at_unsafe :: HyperNum a
                           => Generator a -> Section a s -> (Section a s, Section a s)
section_split_at_unsafe g (SectionUnsafe map n) =
        with_invariant "section_split_at_unsafe"
        precondition
        postcondition
        $ ( SectionUnsafe local ln
          , SectionUnsafe other on
          )
        where
                precondition = n >= 0
                postcondition (local,other) = section_gencount_unsafe local >= 0 &&
                                              section_gencount_unsafe other >= 0

                local = IntervalMap.intersecting map g   -- Doc says O(log n) in average
                ln    = IntervalMap.size local           -- O(n)..
                other = IntervalMap.foldlWithKey del map local -- No foldl'??
                on    = n - ln
                del m g x = assert (IntervalMap.member g m) $ IntervalMap.delete g m


-- | Global validity, O(n)
--   Tests whether it is a section of the constant sheaf Δs
section_valid :: (HyperNum a, Eq s) => Section a s -> Bool
section_valid s =
        let gss              = section_to_asc_components_list s -- :: [[(Generator, s)]]
            coherent         = all open  $ map fst $ concat gss
            locally_constant = all const gss
        in
                section_gencount_unsafe s >= 0 && locally_constant && coherent
        where
                open (Interval.OpenInterval _ _) = True
                open _ = False
                const         = unique . map snd
                unique []     = False
                unique (x:xs) = all (==x) xs

spec_section_valid = it "checks the global validity as a section of a constant sheaf" $ do
        s0  `shouldSatisfy` section_valid
        section_singleton (genA (0,1),1) `shouldSatisfy` section_valid
        section_from_list_unsafe [(genA (0,1),1),(genA (1,2),1)] `shouldSatisfy` section_valid
        section_from_list_unsafe [(genA (0,1),1),(genA (1-dx,2),1)] `shouldSatisfy` section_valid
        section_from_list_unsafe [(genA (0,1),1),(genA (1-dx,2),2)] `shouldSatisfy` not . section_valid


-- | Local validity, O(log n) at best
section_valid_at :: (HyperNum a, Eq s) => Generator a -> Section a s -> Bool
section_valid_at g s =
        let t = section_components_at g s
        in  section_valid t


spec_section_valid_at = it "checks the local validity  as a section of a constant sheaf" $ do
        let s = section_from_list_unsafe

        let s1 = s [(genA (0,1),1),(genA (1,2),2)]

        s1 `shouldSatisfy` section_valid_at (genA (0,dx))


{- | O(n)
     Note that a section is actually an equivalence class,
     with s==s' iff  their canonical representations are equal.
-}

instance (HyperNum a, Eq s) => Eq (Section a s) where
        -- @tbd slow
        s == t = let ms = section_canonicalize s
                     mt = section_canonicalize t
                 in
                         case (ms,mt) of
                         (Just cs, Just ct) -> section_eq_unsafe cs ct
                         _ -> error "(==): not sections; undefined"

spec_section_eq = it "defines the equivalence relation for the representations of sections" $ do
        let s = section_from_list_unsafe

        s0 == s0 @=? True
        s [(genA (0,1),0), (genA (1-dx,2),0)] @=? s [(genA (0,2),0)]


{- |  O(n)
      Canonicalize a section, i.e. transform to the most efficient representation
      while preserving the equality of sections.
-}
section_canonicalize :: (HyperNum a, Eq s) => Section a s -> Maybe (Section a s)
section_canonicalize s =
        with_invariant "section_canonicalize"
        precondition
        postcondition
        mt

        where
                precondition  = section_valid s
                postcondition (Just s) = section_valid s
                postcondition Nothing  = True

                mt  = fmap section_from_list_unsafe $
                      foldr (<:) (Just [])          $
                      map maybe_union               $
                      section_to_asc_components_list s

                Nothing <: _       = Nothing
                _       <: Nothing = Nothing
                Just x  <: Just xs = Just (x:xs)

                maybe_union []     = Nothing
                maybe_union (g:gs) = foldl' (\/) (Just g) gs

                Nothing    \/ _ = Nothing
                Just (s,x) \/ (t,y)
                        | x == y    = Just (gen_union s t, x)
                        | otherwise = Nothing

spec_section_canonicalize = it "transforms a section to the canonical form" $ do
        let s = section_from_list_unsafe
            x @->? y =  (fromJust $ section_canonicalize x) `section_eq_unsafe` y @=? True

        let s1 = s [(genA (0,1),1)]
            s2 = s [(genA (0,1),1)
                   ,(genA (1-dx,2),1)]
            s3 = s [(genA (0,2),1)]
            s4 = s [(genA (0,1),1)
                   ,(genA (0+dx,1-2*dx),1)
                   ,(genA (1-3*dx,2),1)
                   ]
            s5 = s [(genA (0,2),1)]

        s0 @->? s0
        s1 @->? s1
        s2 @->? s3
        s4 @->? s5


{- * Operations on sections

There are two kinds of operations on sections, one for the base
topology  and the other for applying geometric theories (e.g. algebras) 'along the stalk'
that are stable under geometric morphisms.
-}

{- ** Geometric/Topological operations

Geometric/Topological operations include:
1. dealing with connectedness
2. dense covering of the compliment
3. restriction
4. gluing
5. geometric morphisms (direct and inverse images which are adjoint)
6. Compute the area of the domain
-}

-- *** Connected Components

-- | Are two sections disjoint?
section_disjoint :: (HyperNum a , Eq s) => Section a s -> Section a s -> Bool
section_disjoint s t = section_lift2 const s t == section_empty

spec_section_disjoint =
        it "tests whether two sections are disjoint" $ do
                let s1 = section_singleton (genA (0,1),1)
                    s2 = section_singleton (genA (1-dx,2),1)
                    s3 = section_singleton (genA (2,3),1)

                section_disjoint s1 s2 @=? False
                section_disjoint s1 s3 @=? True


-- | Returns the list of connected componenents, represented as a list of generating sections in asc order
section_to_asc_components_list :: HyperNum a => Section a s -> [[(Generator a, s)]]
section_to_asc_components_list s =
        case section_to_asc_list s of
        []         -> []
        ((g,x):gs) -> snd $ foldl' classify (g,[[(g,x)]]) gs

        where
                classify (g, (gs:gss)) (h,y)
                        | gen_intersects g h = (g \/ h, ((h,y):gs):gss)
                        | otherwise          = (h     , [(h,y)]:gs:gss)
                (\/) = gen_union


spec_section_to_asc_components_list =
        it "converts the representation as the list of connected components"  $ do
                let cs = section_to_asc_components_list
                    sc = section_from_list_unsafe
                    has_len n xs = length xs == n

                cs s0 @=? []
                cs (sc [(genA (0,1),0), (genA (1,2),1)])    `shouldSatisfy` has_len 2
                cs (sc [(genA (0,1),0), (genA (1-dx,2),1)]) `shouldSatisfy` has_len 1


-- | Return the list of connected components
section_connected_components :: HyperNum a => Section a s -> [Section a s]
section_connected_components s = map section_from_list_unsafe $ section_to_asc_components_list s

-- | Restrict the section to its connected components intersecting the given generator.
--   Note that there always exists an ordering of generators that respects connected components
--   even in very high dimensional, non-constructive cases (use Zorn's lemma).
section_split_components_at :: (HyperNum a, Eq s)
                               => Generator a -> Section a s -> (Section a s, Section a s)
section_split_components_at g s =
        with_invariant "section_split_components_at"
        precondition
        postcondition
        (local, other)
        where
                precondition  = not (gen_null g) && section_valid s
                postcondition (local, other) = section_valid local &&
                                               section_valid other

                (l, o)   = section_split_at_unsafe g s
                ldom     = foldl1' gen_union $ g:section_domain_asc l  -- @tbd this wont' generalize
                (l', o') = section_split_components_at ldom o        -- recurse

                local | section_null l = l
                      | otherwise      = l \/ l'

                other | section_null l = s
                      | otherwise      = o'

                (\/) = section_glue_unsafe

spec_section_split_components_at =
        it "splits the connected components of a section into two parts" $ do
                let split_at = section_split_components_at
                    s        = section_from_list_unsafe
                    rep      = section_to_tuple_unsafe

                    (x,y) @==? (a,b) = do rep x @=? rep a
                                          rep y @=? rep b

                let g1 = (genA (0,1),0)
                    g2 = (genA (1,2),1)
                    g3 = (genA (2-dx,3),1)
                    s123 = s[g1,g2,g3]
                    s1   = s[g1]
                    s23  = s[g2,g3]

                split_at (genA (0,1)) s0           @==? (s0  , s0)
                split_at (genA (-2,-1))     s123   @==? (s0, s123)
                split_at (genA (-dx,dx))    s123   @==? (s1, s23)
                split_at (genA (3-dx,4))    s123   @==? (s23, s1)
                split_at (genA (1-dx,1+dx)) s123   @==? (s123, s0)




-- | Get the connected components at the generator
section_components_at :: (HyperNum a, Eq s) => Generator a -> Section a s -> Section a s
section_components_at g s =
        let (local, other) = section_split_components_at g s
        in local

spec_section_components_at =
        it "returns the connected components at the generator" $ do
                let s  = section_from_list_unsafe
                let s1 = s [(genA (0,1),0), (genA (1-dx,2),0), (genA (2,3),1)]
                section_components_at (genA (2-dx,2+dx)) s1 @=? s1

{- *** A dense covering of the compliment

In our category, for any object U, the coproduct ∐V    does not exist.
                                                 V∩U=0

However we can 'create the colimit' by considering the stream of growing large-enough
objects that are disjoint to U:

Uᶜ° = [V0,V1,..| Vi∩U == 0, closure(std(Vi∪U)) == std(A), Vi -> V(i+1)]
s.t. if W∩U == 0 then there is some i such that W -> Vi.

(Here std is the continuous projection onto the standard part of the base hyperreal ring A.)

-}

-- | [O(n),O(log n),O(log n),..] (but not now)
--   The first element is already 'large enough' that it densely covers the standard part of the complement.
--   (i.e. the union of the argument and any of the elements of the list will cover (-inf,inf) 'densely'.)
--   Note that this function is not so trivial and will be costly in higher dimensional cases.. what to do?
section_compliments :: (HyperNum a, Eq s) => Section a s -> [Section a Singleton]
section_compliments s =
        with_invariant "section_compliments"
        precondition
        postcondition
        $ map (section_from_list_unsafe . cover boundaries) [1..]
        where
                precondition = section_valid s
                postcondition (sc:_) = sc `section_disjoint` s' &&
                                       area (std /\ (sc \/ s')) == area std
                        where
                                s'     = section_lift1 (const ()) s
                                std    = section_singleton (gen (-inf,inf),())
                                x \/ y = fromJust $ section_glue x y
                                x /\ y = fromJust $ section_restrict x y
                                area = section_area

                boundaries = section_boundary_points_asc s -- even

                cover [] n = [(gen (-inf^n,inf^n), ())]
                cover bs n = let b0 = head bs
                                 bn = head (reverse bs)
                                 cs = [(-2*inf^n+b0)] ++ bs ++ [(bn+2*inf^n)] -- even
                                 gs = filter (not . gen_null) $ map gen $ take_odd $ pair cs
                             in
                                     zip gs (repeat ())

                pair xs = zip xs (tail xs)
                take_odd [x]      = [x]
                take_odd (x:y:xs) = x:take_odd xs

spec_section_compliments =
        it "computes the ascending chain of large-ish compliments" $ do
                let s  = section_from_list_unsafe
                    cs = section_compliments
                    z  = ()

                let s1 =  s [(genA (0,1),0),(genA (2,3),1)]
                    s2 =  s [(genA (0,1),0),(genA (1,3),1)]

                head (cs s1) @=? s [(genA (-2*inf,0),z),(genA (1,2),z),(genA (3,3+2*inf),z)]
                head (cs s2) @=? s [(genA (-2*inf,0),z),(genA (3,3+2*inf),z)]

gen_compliments :: HyperNum a => Generator a -> [Section a ()]
gen_compliments g = section_compliments $ section_singleton (g,())


-- Only meaningful for 1-dim
section_boundary_points_asc :: HyperNum a => Section a s -> [a]
section_boundary_points_asc s = concat $ map to_list $ section_domain_asc s
        where
                to_list g = let (x,y) = from_gen g
                            in  [x,y]

-- *** Restriction

-- Restrict the generating sections to given generator
gen_restrict_at :: HyperNum a => Generator a -> [(Generator a, s)] -> [(Generator a, s)]
gen_restrict_at g gs = concat $ map (restrict g) gs
        where
                restrict g (s,x)
                        | gen_disjoint g s = []
                        | otherwise        = [(g/\s,x)]

                (/\) = gen_intersection

spec_gen_restrict_at =
        it "restricts generating sections to a generator" $ do
                let r = gen_restrict_at

                r (genA (0,1)) [(genA (-1,2),1)] @=? [(genA (0,1),1)]
                r (genA (0,1)) [(genA (1 ,2),1)] @=? []

-- Restrict the generating sections to the given generating section
gen_restrict_at_consistently :: (HyperNum a, Eq s)
                                => Generator a -> s -> [(Generator a, s)] -> Maybe [(Generator a, s)]
gen_restrict_at_consistently g y gs = concat_maybes $ map (restrict g) gs
        where
                restrict g (s,x)
                        | gen_disjoint g s = Just []
                        | x == y           = Just [(g/\s,x)]
                        | otherwise        = Nothing

                concat_maybes = foldl' (+) (Just [])

                Nothing + _ = Nothing
                _ + Nothing = Nothing
                (Just xs) + (Just ys) = Just (xs++ys)

                (/\) = gen_intersection

spec_gen_restrict_at_consistently =
        it "restricts generating sections to the given generating section" $ do
                let r = gen_restrict_at_consistently

                r (genA (0,1)) 1 [(genA (-1,2),1)] @=? Just [(genA (0,1),1)]
                r (genA (0,1)) 2 [(genA (-1,2),1)] @=? Nothing
                r (genA (0,1)) 1 [(genA (1 ,2),1)] @=? Just []


-- | O(log n) at best
--   Restrict section s to generator g
section_restrict_at :: (HyperNum a, Eq s)
                       => Generator a -> Section a s -> Section a s
section_restrict_at g s =
        with_invariant "section_restrict_at"
        precondition
        postcondition
        t
        where
                precondition  = not (gen_null g) && section_valid s
                postcondition = section_valid

                (local, other) = section_split_at_unsafe g s

                t   = section_from_list_unsafe $ gen_restrict_at g $ section_to_asc_list local

spec_section_restrict_at =
        it "restricts a section to the given generator" $ do
                let r = section_restrict_at
                    s = section_from_list_unsafe

                let s1 = s [(genA (0,1),0), (genA (1,2),1), (genA (2,3),2)]

                r (genA (-dx,0))  s1 @=? s0
                r (genA (-dx,dx)) s1 @=? s [(genA (0,dx), 0)]
                r (genA (1-dx,3-dx)) s1 @=? s [(genA (1-dx,1),0), (genA (1,2),1), (genA (2,3-dx),2)]

-- | O(log n) at best
--   Restrict a section to a generating section; returns 'Nothing' if it cannot be done in consistent way.
section_restrict_at_consistently :: (HyperNum a, Eq s)
                                    => Generator a -> s -> Section a s -> Maybe (Section a s)
section_restrict_at_consistently g x s =
        with_invariant "section_restrict_at_consistently"
        precondition
        postcondition
        t
        where
                precondition  = not (gen_null g) && section_valid s
                postcondition Nothing  = True
                postcondition (Just s) = section_valid s

                (local, other) = section_split_at_unsafe g s

                t   = fmap section_from_list_unsafe    $
                      gen_restrict_at_consistently g x $
                      section_to_asc_list local

spec_section_restrict_at_consistently =
        it "restricts a section to the given generating section " $ do
                let r = section_restrict_at_consistently
                    s = section_from_list_unsafe

                let s1 = s [(genA (0,1),0), (genA (1,2),1), (genA (2,3),2)]

                r (genA (-dx,0)) 0  s1 @=? Just s0
                r (genA (-dx,dx)) 0 s1 @=? Just (s [(genA (0,dx), 0)])
                r (genA (1-dx,3-dx)) 0 s1 @=? Nothing


-- | O(n*log m) at best (should be optimized)
--   Restrict a section to another section, returning Nothing on failure.
section_restrict :: (HyperNum a, Eq s)
                    => Section a s -> Section a s -> Maybe (Section a s)
section_restrict s t = -- @tbd the choose larger section for efficiency
        with_invariant "section_restrict"
        precondition
        postcondition
        mu
        where
                precondition    = section_valid s && section_valid t
                postcondition Nothing  = True
                postcondition (Just s) = section_valid s

                mu  = try_union $ map (restrict s) $ section_to_asc_list t

                try_union = foldl' (\/) (Just section_empty)

                Nothing \/ _ = Nothing
                _ \/ Nothing = Nothing
                (Just s) \/ (Just t) = Just (section_glue_unsafe s t)

                restrict s (g,x) = section_restrict_at_consistently g x s

spec_section_restrict =
        it "restricts a section to a section" $ do
                let r = section_restrict
                    s = section_from_list_unsafe

                let s1 = s [(genA (0,1),0), (genA (1,2),0), (genA (2,3),2)]
                r s1 s0 @=? Just s0
                r s1 (s [(genA (-inf,0),0)]) @=? Just s0
                r s1 (s [(genA (-inf,dx),1)]) @=? Nothing

                r s1 (s [(genA (1-dx,1+dx),0),
                         (genA (3-dx,inf),2)]) @=? Just (s [(genA (1-dx,1),0)
                                                          ,(genA (1,1+dx),0)
                                                          ,(genA (3-dx,3),2)
                                                          ])


-- | Does x subsumes y, i.e. does x restrict to y?
section_subsumes :: (HyperNum a, Eq s)
                    => Section a s -> Section a s -> Bool
section_subsumes s t =
        case section_restrict s t of
        Just t' ->  t' == t
        Nothing ->  False


-- *** Gluing

-- | Glue two generating sections
--   The result is undefined if either of the arguments is a section on the initial object
--   (because Δs(0) == 1 and s is considered different to 1 no matter what s is)
gen_glue :: (HyperNum a, Eq s)
            => (Generator a, s) -> (Generator a, s) ->  Maybe (Section a s)
gen_glue (g,x) (h, y)
        |  gen_disjoint g h = Just $ section_from_list_unsafe [(g,x),(h,y)]
        |  x == y           = Just $ section_from_list_unsafe [(g\/h,x)]
        |  x /= y           = Nothing

        where (\/) = gen_union

spec_gen_glue =
        it "glues two generating sections together" $ do
                let s = section_from_list_unsafe
                gen_glue (genA (0,1), 0) (genA (1-dx,2),1) @=? Nothing
                gen_glue (genA (0,1), 0) (genA (1-dx,2),0) @=? Just (s [(genA (0,2), 0)])
                gen_glue (genA (0,1), 0) (genA (1   ,2),1) @=? Just (s [(genA (0,1), 0), (genA (1,2),1)])


-- | O(log n) at best
--  Glue a section with a generating section
section_glue_at :: (HyperNum a, Eq s)
                   => Generator a -> s -> Section a s -> Maybe (Section a s)
section_glue_at g x s =
        with_invariant "section_glue_at"
        precondition
        postcondition
        ms

        where
                precondition = not (gen_null g) && section_valid s
                postcondition Nothing  = True
                postcondition (Just s) = section_valid s

                (local, other) = section_split_at_unsafe g s

                mlocal = fmap fromJust $
                         fmap section_canonicalize        $
                         foldl' (\/) (Just section_empty) $
                         map (gen_glue (g,x))             $
                         (g,x):section_to_asc_list local

                ms = case mlocal of
                        Nothing -> Nothing
                        Just s  -> Just other \/ Just s

                _        \/ Nothing = Nothing
                Nothing  \/ _       = Nothing
                (Just x) \/ (Just y) = Just (section_glue_unsafe x y)

spec_section_glue_at =
        it "glues a section with a generating section" $ do
                let s = section_from_list_unsafe

                let s1 = s [(genA (0,1), 0), (genA (2,3), 0)]
                section_glue_at (genA (-dx,dx)) 1 s0 @=? Just (s [(genA (-dx,dx),1)])
                section_glue_at (genA (-dx,dx)) 1 s1 @=? Nothing
                section_glue_at (genA (-dx,dx)) 0 s1 @=? Just (s [(genA (-dx,1),0),(genA (2,3),0)])
                section_glue_at (genA (1-dx,2+dx)) 0 s1 @=? Just (s [(genA (0,3),0)])



-- | O(n*log m) at best, should be optimized
--   Glue two sections together
section_glue :: (HyperNum a, Eq s)
                => Section a s -> Section a s -> Maybe (Section a s)
section_glue s t =
        with_invariant "section_glue"
        precondition
        postcondition
        mu

        where
                precondition = section_valid s && section_valid t
                postcondition Nothing  = True
                postcondition (Just s) = section_valid s

                mu | s `section_smaller_unsafe`  t = t <* s
                   | otherwise                     = s <* t

                x <* y = section_foldl'_unsafe (\/) (Just x) y

                Nothing  \/ _     = Nothing
                (Just s) \/ (g,x) = section_glue_at g x s

spec_section_glue =
        it "glues two sections together" $ do
                let s = section_from_list_unsafe

                let s1 = s [(genA (0,1), 0), (genA (2,3), 1)]
                    s2 = s [(genA (-dx,dx),0), (genA (2,3+dx),1)]
                    s3 = s [(genA (-dx,dx),0), (genA (1-dx,2+dx), 1), (genA (2,3+dx),1)]

                section_glue s1 s0 @=? Just s1
                section_glue s1 s2 @=? Just (s [(genA (-dx,1),0),(genA (2,3+dx),1)])
                section_glue s1 s3 @=? Nothing


-- *** Geometric Morphisms

-- **** Continuous group actions on the base space

instance (HyperNum a, HyperSet a) => HyperSet (Interval a) where
        hyper_act_left x iv = gen $ hyper_act_left x (from_gen iv)


-- | Compute the direct image of the continuous group action (+x)*
section_translate :: (HyperNum a, HyperSet a)
                     => Hyper Integer -> Section a s -> Section a s
section_translate x s = section_from_list_unsafe $ map (translate x) $ section_to_asc_list s
        where
                translate x (g,s) = (hyper_act_left x g, s)


spec_section_translate =
        it "compute the direct image under the continuous action (+x)*" $ do
                let s  = section_from_list_unsafe
                    s *> x = section_translate x s

                let s1 = s [(genA(0,1),0),(genA(2,3),1)]

                s1 *> 10 @=? s [(genA(10,11),0),(genA(12,13),1)]

-- *** Geometry of the sections

-- | Area of a generator
gen_area :: HyperNum a => Generator a -> a
gen_area g = gen_upper_bound g - gen_lower_bound g

-- | Area of a section
section_area :: (HyperNum a) => Section a s -> a
section_area s = foldl' (+) 0 $ map gen_area $ section_domain_asc s

spec_section_area =
        it "computes the area of a section" $ do
                let s = section_from_list_unsafe

                section_area (s [(genA(0,1),0),(genA(2,4),1)]) @=? 3

{- ** Algebraic operations

The theory to be lifted should be geometric in the sense given at Note,
so that they are stable under geometric morphisms.
For example, it should not rely on a property expressed by an infinite number of
conjunctions.

-}


-- | Unary operation. O(n)
--   'Nothing' specifies that the corresponding domains should be deleted.
section_lift1_partial :: (HyperNum a, Eq s)
                         => (s -> Maybe t) -> Section a s -> Section a t
section_lift1_partial f s  =
        with_invariant "section_lift1_partial"
        precondition
        postcondition
        t

        where
                precondition     = section_valid s
                postcondition s  = True

                t = SectionUnsafe (IntervalMap.fromDistinctAscList gs) n

                (gs,n) = IntervalMap.foldrWithKey push ([],0) $ section_genmap_unsafe s

                push g x (gs,n) =
                        case f x of
                        Just y  -> ((g,y):gs, force $ n+1)
                        Nothing -> (gs,n)

                force x = x `seq` x

spec_section_lift1_partial =
        it "lifts a geometric theory on s to a 'Section s'" $ do
                let lift = section_lift1_partial
                    s    = section_from_list_unsafe

                let s1 = s [(genA (0,1), 0), (genA (2,3), 1)]
                    f x  | x == 0    = Nothing
                         | otherwise = Just (x+1)

                lift f s0 @=? s0
                lift f s1 @=? s [(genA (2,3),2)]

-- | O(n)
--   Unary operation.
section_lift1 :: (HyperNum a, Eq s)
                 => (s -> t) -> Section a s -> Section a t
section_lift1 f s  = section_lift1_partial f' s
        where f' x = Just (f x)

-- | O(n*log m) @tbd much much room left for optimization
--   Binary operation.
section_lift2_partial :: (HyperNum a, Eq s, Eq t, Eq u)
                         => (s -> t -> Maybe u) -> Section a s -> Section a t -> Section a u
section_lift2_partial (*) s t =
        with_invariant "section_lift2_partial"
        precondition
        postcondition
        u
        where
                precondition      = section_valid s && section_valid t
                postcondition u   = section_valid u

                u = section_from_list_unsafe $
                    concat            $
                    map (apply (*))   $
                    map (s /\)        $
                    section_to_asc_list t -- @tbd slow, do bisecting

                s /\ (g,x) = let (local, other) = section_split_at_unsafe g s
                             in  zip (section_to_asc_list local) (repeat (g,x))

                apply (*) gs = let process ((g,x),(h,y)) = listify (g/\h) (x*y)
                                   listify _ Nothing     = []
                                   listify g (Just x) | gen_null g = []
                                                      | otherwise  = [(g,x)]
                                   (/\)  = gen_intersection

                               in concat $ map process gs


spec_section_lift2_partial =
        it "lifts a (geometric) binary operation to constant sheaves " $ do
                let lift2 = section_lift2_partial
                    s     = section_from_list_unsafe

                let s1 = s [(genA (0,1), 0), (genA (2,3), 1)] :: Section A Int
                    s2 = s [(genA (-inf,dx),10),(genA (1-dx,2+dx),20)] :: Section A Int
                    f x 10 = Nothing
                    f x y  = Just (x+ y)

                lift2 f s1 s2 @=? s [(genA (1-dx,1),20), (genA (2,2+dx),21)]


-- | Lift a binary operation
section_lift2 :: (HyperNum a, Eq s, Eq t, Eq u)
                 => (s -> t -> u) -> Section a s -> Section a t -> Section a u
section_lift2 (*) s t = section_lift2_partial (**) s t
        where x ** y = Just (x*y)
