module Sheaf
where
import Pretty
import Hyper
import Invariant

import Data.List

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

 One of the fascinating ideas in Math is the study of
 complicated algebraic/logical  structures under the light  of
 human geometric/topological intuition.

 The goal of this library is exactly this; it tries to 'geometrize' data structures
 with the help of Grothendieck topologies.

 We will try to unify and generalize Lists, Trees, Maps, Sets, IntervalMaps, Continuations, or
 any combination of them, etc.,etc.. in order to give them 'geometric studies'.

 If some data structure could be pictorized on paper, chances are that its 'geometry'
 may be modeled by a sheaf on a site with a (often coherent) computable
 description of its 'topology'.

 Examples include the time series of Sets/Maps, Maps over decidable
 sets (whose algebra, i.e. the boolean lattice of decidable sets,
 corresponds to a boolean continuation monad making it a  boolean topos),
 Maps over 'local ordering' patched together (e.g. the unit circle), and
 of cource "the time series of trees of virtual address spaces" as in
 our example program.

 With sheaves it should be possible to model processes with shared memory,
 processes on NUMA systems, distributed systems, in a way that strongly reflects the
 programmer's natural geometrical/topological intuition.

 Sheaves also generalize monads (or any 'geometric theory'), but
 probably not in Haskelly way (because categorical programming in Haskell
 often seems a bit cranky and unnatural.. but I really don't know.)

 As a start, in this library I will concentrate on constant sheaves on a
 constructive site.

* How to compute constant sheaves on a constructive site

The purpose of this note is to explain (to myself) how constant sheaves are
derived constructively from a computable description of a site.
Please at least take a quick look at the section 5, because if the arguments there were wrong,
the code given below would be too.

Contents
0. Notation
1. An Example
2. Sheaves on a Site
3. The Associated Sheaf Functor
4. Constant Sheaves and Global Sections
5. Construction of Constant Sheaves
6. Examples of Constant Sheaves
7. Sections of Constant Sheaves
8. Geometric Morphisms between Constant Sheaves
9. Geometric Theories on Constant Sheaves

References:
[1] S.MacLane, I.Moerdijk, Sheaves in Geometry and Logic
[2] P.Johnstone, Sketches of an Elephant: A Topos theory Compendium


* 0. Notation

Because relative sizes of unicode characters are not standardized,
I will use ASCII characters almost exclusively where the correct
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
3. I like c and ocaml..

* 1. An Example

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

* 2. Sheaves on (C,K)

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
      r1 :: F(X) -> F(X1)
      r1 = F(X1 -> X)
      r2 :: F(X) -> F(X2)
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

* 3. The Associated Sheaf Functor

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

* 4. Constant Sheaves and Global Sections

Let S be a set.
The constant presheaf ΔS is the contravariant functor in Psh(C) s.t.
ΔS(X) = S and ΔS(X->Y) = id for all X,Y in C.

A constant sheaf (on a site (C,K)) is the sheafification a(ΔS) of
a constant presheaf ΔS, and also denoted ΔS when no confusion will arise.

Δ, considered as a functor from Sets to Sh(C,K), has a right adjoint Γ:

Δ:Sets <--> Sh(C,K):Γ

where Γ is the natural transformation Hom(Δ1,-), called the global
section functor. (Note that the presheaf Δ1 is already a sheaf.)

The constant sheaves are actually our main data structure, so we shall calculate them explicitly.
Intuitively, it should be obvious, it's a sheaf of 'locally constant' functions discussed below.

* 5. Construction of Constant Sheaves

WARNING:
  Careful, this is my own. You'll find mistakes!
  The biggest trouble is that 'disjoint sieves' don't (easily) make sense and
  don't seem to be representable.


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

* 6. Examples of Constant sheaves

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

* 7. Sections of Constant Sheaves

Hereafter ΔS will denote the constant sheaf again.

A section x on X of a sheaf F is an element x in F(X).

To emphasize concreteness, here I
concentrate on sections of constant sheaves on the site (C,K) given
in Section 1., in a way that could facilitate further generalizations.

objects  : finite unions of open intervals in A, including the empty set.
morphisms: inclusion as sets.
K(X) = the combinations of maximal disjoint intervals which cover X.

-}

-- | The base space
type A         = Hyper Integer

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
so let us just call them 'generators' (or maybe should we just call them 'generalized elements'?).

In the sequel, I will add the suffix '_at' to the name of an operation of a section
that acts locally near the given generator, in order to emphasize that our generating family
is considered as a collection of points.

-}

{- |
As noted above, it is essential that our generating family only contains open intervals.
Otherwise its sections must necessarily include step functions with infinite number of jumps,
in which case the representation of sections as the finite map of intervals would be insufficient.
-}

type OpenInterval = Interval A
type Generator    = OpenInterval

-- induce algebras from the dst space
induce0 :: (a -> b) -> (c) -> (c -> d) -> d
induce0 from x0 to = to (x0)

induce1 :: (a -> b) -> (b -> c) -> (c -> d) -> a -> d
induce1 from f to = \x -> to (f (from x))

induce2 :: (a -> b) -> (b -> b -> c) -> (c -> d) -> a -> a -> d
induce2 from (*) to = \x y -> to (from x * from y)

gen :: (A,A) -> Generator
gen (x,y) = Interval.OpenInterval x y

from_gen :: Generator -> (A,A)
from_gen (Interval.OpenInterval x y) = (x,y)

gen_empty :: Generator
gen_empty = induce0
            from_gen
            hyper_interval_empty
            gen

gen_null  :: Generator -> Bool
gen_null = induce1
           from_gen
           hyper_interval_null
           id

gen_unions :: Generator -> Generator -> [Generator]
gen_unions = induce2
             from_gen
             hyper_interval_union
             (map gen)

-- partial, dangerous
gen_union  :: Generator -> Generator -> Generator
gen_union  = induce2
             from_gen
             hyper_interval_union
             (head . map gen)

gen_intersection :: Generator -> Generator -> Generator
gen_intersection = induce2
                   from_gen
                   hyper_interval_intersection
                   gen

gen_disjoint :: Generator -> Generator -> Bool
gen_disjoint = induce2
               from_gen
               hyper_interval_disjoint
               id

gen_intersects :: Generator -> Generator -> Bool
gen_intersects = induce2
                 from_gen
                 hyper_interval_disjoint
                 not


{-|
Next we recall that

Δs(X) = colim(Hom(R,s))
          R in KD(X)^op

which is a set of equivalence classes represented by (f::R->s) for R
a set of disjoint covers {c::U->X}. Since on our site a disjoint
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
data Section s = Section
                 { section_data     :: IntervalMap A s -- Open intervals only
                 }
               deriving (Show)

section_to_asc_list :: Section s -> [(Generator, s)]
section_to_asc_list (Section section_data) = IntervalMap.toAscList section_data

section_from_list :: [(Generator, s)] -> Section s
section_from_list gs = Section (IntervalMap.fromList gs)

section_domain_asc :: Section s -> [Generator]
section_domain_asc = map fst . section_to_asc_list

-- | Glueing without checking
section_glue_unsafe :: Section s -> Section s -> Section s
section_glue_unsafe s s' = Section $ IntervalMap.union (section_data s) (section_data s')

section_null :: Section s -> Bool
section_null s = IntervalMap.null $ section_data s

section_empty :: Section s
section_empty = Section (IntervalMap.empty)

{- |
The most basic building block for defining topological operations
to ensure reasonable computational complexity (e.g. O((log n)^d) for a dimension d).
Note that this itself is not a well-defined topological operation.

It splits the section into three parts: one below (in a sense) the generator,
one intersecting the generator, and the other above the generator.
The three may not necessarily be disjoint; so this doesn't topologically make sense.
-}
section_split_at_unsafe :: Generator -> Section s -> (Section s, Section s, Section s)
section_split_at_unsafe g (Section section_data) =
        let (below, s, above) =  IntervalMap.splitIntersecting section_data g
        in
                (Section below, Section s, Section above)

-- | Global validity, O(n)
section_valid :: Eq s => Section s -> Bool
section_valid s =
        let gss              = section_connected_components_gen s -- :: [[(Generator, s)]]
            coherent         = all open  $ map fst $ concat gss
            locally_constant = all const gss
        in
                locally_constant && coherent
        where
                open (Interval.OpenInterval _ _) = True
                open _ = False
                const         = unique . map snd
                unique []     = False
                unique (x:xs) = all (==x) xs


-- | Local validity, O(log n) at best
section_valid_at :: Eq s => Generator -> Section s -> Bool
section_valid_at g s =
        let t = section_components_at g s
        in  section_valid t


{- |
Note that a section is actually an equivalence class,
with s==s' iff  s and s' 'match' in the following sense:
-}

instance Eq s => Eq (Section s) where
        -- @tbd slow
        s == t = let ms = section_canonicalize s
                     mt = section_canonicalize t
                  in
                          section_data ms == section_data mt


section_canonicalize :: Eq s => Section s -> Section s
section_canonicalize s =
        with_invariant "section_canonicalize"
        precondition
        postcondition
        t

        where
                precondition  = section_valid s
                postcondition = section_valid

                t  = section_from_list $ map union $ section_connected_components_gen s

                union gs = foldl1' (\/) gs

                (s,x) \/ (t,y) | x == y    = (gen_union s t, x)
                               | otherwise = error "impossible"

{- |

There are two kinds of operations on sections, one for the base
topology  and the other being geometric theories (e.g. algebra) 'along the stalk'
that are stable under geometric morphisms.

Topological operations include:
1. manimulate or query connected components of a section
2. restrict the domain of a section
3. glue sections
4. geometric morphisms (direct and inverse images)
-}

-- Topological

-- | Returns the list of connected componenents, represented as a list of sections on generators
section_connected_components_gen :: Section s -> [[(Generator, s)]]
section_connected_components_gen s =
        case section_to_asc_list s of
        []         -> []
        ((g,x):gs) -> snd $ foldl' classify (g,[[(g,x)]]) gs

        where
                classify (g, (gs:gss)) (h,y)
                        | gen_intersects g h = (g \/ h, ((h,y):gs):gss)
                        | otherwise          = (h     , [(h,y)]:gs:gss)
                (\/) = gen_union

-- | Return the list of connected components
section_connected_components :: Section s -> [Section s]
section_connected_components s = map section_from_list $ section_connected_components_gen s

-- | Restrict the section to its connected components intersecting the given generator
--   Note that there always exists an ordering of generators that respects connected components
--   even in higher dimensional cases (use Zorn's lemma).

section_split_components_at :: Eq s => Generator -> Section s -> (Section s, Section s, Section s)
section_split_components_at g s =
        with_invariant "section_components"
        precondition
        postcondition
        t
        where
                precondition  = not (gen_null g) && section_valid s
                postcondition (below,local,above) = section_valid below &&
                                                    section_valid local &&
                                                    section_valid above

                t =  let (below, local, above) = section_split_at_unsafe g s
                         h                     = foldl1' gen_union $ section_domain_asc local
                         (bb, bl, ba)          = section_split_components_at h below
                         (ab, al, aa)          = section_split_components_at h above
                     in
                             if section_null local
                             then (below, local, above)
                             else
                                     if section_null ba && section_null ab
                                     then (bb   , bl\/local\/al, aa)
                                     else error "section_split_components:impossible"

                (\/) = section_glue_unsafe

section_components_at :: Eq s => Generator -> Section s -> Section s
section_components_at g s =
        let (below, local, above) = section_split_components_at g local
        in local


gen_restrict_at :: Generator -> [(Generator, s)] -> [(Generator, s)]
gen_restrict_at g gs = concat $ map (restrict g) gs
        where
                restrict g (s,x)
                        | gen_disjoint g s = []
                        | otherwise        = [(g/\s,x)]

                (/\) = gen_intersection

gen_restrict_at_consistently :: Eq s => Generator -> s -> [(Generator, s)] -> Maybe [(Generator, s)]
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


section_restrict_at :: Eq s => Generator -> Section s -> Section s
section_restrict_at g s =
        with_invariant "section_restrict_at"
        precondition
        postcondition
        s'
        where
                precondition  = not (gen_null g) && section_valid s
                postcondition = section_valid

                (below, local, above) = section_split_at_unsafe g s
                s'                    = section_from_list $ gen_restrict_at g $ section_to_asc_list local

section_restrict_at_consistently :: Eq s => Generator -> s -> Section s -> Maybe (Section s)
section_restrict_at_consistently g x s =
        with_invariant "section_restrict_at_consistently"
        precondition
        postcondition
        t
        where
                precondition  = not (gen_null g) && section_valid s
                postcondition Nothing  = True
                postcondition (Just s) = section_valid s

                (below, local, above) = section_split_at_unsafe g s

                t   = fmap section_from_list           $
                      gen_restrict_at_consistently g x $
                      section_to_asc_list local


section_restrict :: Eq s => Section s -> Section s -> Maybe (Section s)
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


-- | Gluing

gen_glue :: Eq s => (Generator, s) -> (Generator, s) ->  Maybe (Section s)
gen_glue (g,x) (h, y)
        |  gen_disjoint g h = Just $ section_from_list [(g,x),(h,y)]
        |  x == y           = Just $ section_from_list [(g\/h,x)]
        |  x /= y           = Nothing

        where (\/) = gen_union

section_glue_at :: Eq s => Generator -> s -> Section s -> Maybe (Section s)
section_glue_at g x s =
        with_invariant "section_glue_at"
        precondition
        postcondition
        ms

        where
                precondition = not (gen_null g) && section_valid s
                postcondition Nothing  = True
                postcondition (Just s) = section_valid s

                (below, local, above) = section_split_at_unsafe g s

                mlocal = fmap section_canonicalize        $
                         foldl' (\/) (Just section_empty) $
                         map (gen_glue (g,x))             $
                         section_to_asc_list local

                ms = case mlocal of
                        Nothing -> Nothing
                        Just s  -> Just below \/ Just s \/ Just above

                _        \/ Nothing = Nothing
                Nothing  \/ _       = Nothing
                (Just x) \/ (Just y) = Just (section_glue_unsafe x y)


section_glue :: Eq s => Section s -> Section s -> Maybe (Section s)
section_glue s t =
        with_invariant "section_glue"
        precondition
        postcondition
        mu

        where
                precondition = section_valid s && section_valid t
                postcondition Nothing  = True
                postcondition (Just s) = section_valid s

                mu = foldl' (\/) (Just s) $ section_to_asc_list t

                Nothing  \/ _     = Nothing
                (Just s) \/ (g,x) = section_glue_at g x s

-- @tbd geometric (auto)morphisms

{- |
Algebraic operations.
Any geometric theory on s will naturally carry over to 'Section s'.
(i.e. stable under geometric morphisms)
-}


-- | Unary operation. O(n)
section_lift1_partial :: Eq s => (s -> Maybe t) -> Section s -> Section t
section_lift1_partial f s  =
        with_invariant "section_lift1_partial"
        precondition
        postcondition
        t

        where
                precondition     = section_valid s
                postcondition s  = True

                t = Section $ IntervalMap.mapMaybe f $ section_data s


section_lift1 :: Eq s => (s -> t) -> Section s -> Section t
section_lift1 f s  = section_lift1_partial f' s
        where f' x = Just (f x)

-- | Binary operation. O(n+m)
--   @tbd much much room left for optimization
section_lift2_partial :: (Eq s, Eq t, Eq u) => (s -> t -> Maybe u) -> Section s -> Section t -> Section u
section_lift2_partial (*) s t =
        with_invariant "section_lift2_partial"
        precondition
        postcondition
        u
        where
                precondition      = section_valid s && section_valid t
                postcondition u   = section_valid u

                u = section_from_list $
                    concat            $
                    map (apply (*))   $
                    map (s /\)        $
                    section_to_asc_list t -- @tbd slow, do bisecting

                s /\ (g,x) = let (sb, sl, sa) = section_split_at_unsafe g s
                             in  zip (section_to_asc_list sl) (repeat (g,x))

                apply (*) gs = let process ((g,x),(h,y)) = listify (g/\h) (x*y)
                                   listify _ Nothing     = []
                                   listify g (Just x) | gen_null g = []
                                                      | otherwise  = [(g,x)]
                                   (/\)  = gen_intersection

                               in concat $ map process gs


section_lift2 :: (Eq s, Eq t, Eq u) => (s -> t -> u) -> Section s -> Section t -> Section u
section_lift2 (*) s t = section_lift2_partial (**) s t
        where x ** y = Just (x*y)
