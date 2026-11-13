# T001: a presentation of the unmeasured tensor kernel

Current export status: both positive kernel congruences and both actual
ring-kernel ideals are now proved. See the dated export section at the
end; earlier pending-work notes below preserve their historical status.

This answers the author's follow-up asking for generators of the kernel of
Psi. It is a mathematical calculation in the fixed-ground ACVF(0,0)
categories of Section 3. The equality with the whole kernel is not yet an
exported Lean theorem. In particular, this note does not turn the former
injectivity target into an assumption, or claim that the local Lean
generic-fibre theorems already include the compactness argument below.
No HK result is used as a premise. The working manuscript is unchanged.

## Statement

Fix the original parameter structure S. Put

    T+ = K+ RES[*] tensor_(K+ Gamma^fin[*]) K+ Gamma[*],
    T  = K  RES[*] tensor_(K  Gamma^fin[*]) K  Gamma[*].

All objects, maps and isomorphisms below are S-definable. Write Psi+ and
Psi for the positive and groupified unmeasured maps, respectively.
For a Gamma point delta, notation delta^sharp means the whole fibre
of RV^times -> Gamma, also when delta=0. Thus 0^sharp is G_m, not a
singleton. Let U be an object of Gamma[m], m>=1, and let e_i be a coordinate
unit vector. The translate U+delta e_i has the same degree m.

Define

    Lambda_X = {delta in dcl(S) cap Gamma :
                there is an S-definable c:X -> delta^sharp}.

Take X in RES[r], delta in Lambda_X, U in Gamma[m], and a coordinate i.
The generator, of degree r+m, is

    g(X,delta,U,i) = [X]_r tensor ([U]_m - [U+delta e_i]_m).

Then

    ker(Psi) = ( g(X,delta,U,i) : delta in Lambda_X ).           (K)

The author's notation correction is incorporated here: the generator
depends on delta, not on a chosen function c. Existence of such a c is
the condition delta in Lambda_X; c witnesses a bijection proving kernel
membership. Any two witnesses of the same value give the same displayed
element. The label on X is retained, and a witness c need not be that
label or finite-to-one.

This is a geometric, potentially redundant family
of generators, not a claim of finite generation or a minimal generating
set. It ranges over actual RES objects in every degree. The finite-only
restriction is false in general, by the balanced genus-two curve
detector in `TENSOR-KERNEL-FINITE-COEFFICIENTS.md`. This does not assert
minimality of the whole family. A map c can equivalently be made a
coordinate projection by replacing X with its definable graph, which is
the same RES object up to isomorphism.

For nonempty X, Lambda_X is a subgroup: multiply or invert the functions
c. It contains the values of RV elements definable over S. A generator
using such an original-ground RV value is already zero in T, because the
translation is an allowed Gamma morphism. The possibly new relations
occur when the multiplier is available as a function of x in X, although
it is not available over S alone.

For the positive semiring, the appropriate assertion is a congruence:

    Psi+(a)=Psi+(b) iff a and b are congruent under the relations

    [X]_r tensor [U]_m ~ [X]_r tensor [U+delta e_i]_m,            (K+)

with the same data. A semiring kernel congruence must not be confused
with the inverse image of zero. Here the latter is just {0}: each
positive tensor is a finite sum of actual product objects, and an empty
such RV object has only empty product summands. Valuation onto Gamma is
surjective. Noninjectivity therefore concerns two nonzero positive
classes with the same image, and becomes a nonzero ideal after
groupification.

## Why every displayed generator belongs to the kernel

Fix delta in Lambda_X and choose a witness c:X -> delta^sharp.
The map

    (x,u_1,...,u_m) |->
      (x,u_1,...,c(x) u_i,...,u_m)

is an original-ground definable RV bijection from X x U^sharp to
X x (U+delta e_i)^sharp. Its inverse divides the i-th coordinate by
c(x). Both objects have degree r+m; morphisms in the unmeasured RV
category do not have to commute with their finite labels. This proves
the inclusion of the ideal in ker(Psi), and validity of (K+) in RV.

## Local form needed for the reverse inclusion

The point of this calculation is that an RV multiplier may depend on the
RES point. It is never replaced by a multiplier over S alone.

Here are the fixed-ground normal-form facts used in the calculation.
They follow from the locally proved angular product decomposition,
generic full-value-fibre invariance, and integral monomial rigidity.
They are not applications of HK Claim 3 as an accepted theorem.

1. A RES set has finite Gamma support, is stable, and adjoining a point of
   it does not enlarge Gamma-definable closure of the original ground.
   A definable relation between a RES set and a Gamma power is a finite
   union of definable rectangles. In particular a definable function from
   RES to Gamma has finite image. Every element of a finite S-definable
   Gamma set is S-definable, using its definable order.
2. Let p be a complete type of a Gamma m-tuple with no nontrivial integral
   affine relation over Gamma-definable closure of S. Its full RV
   preimage is a complete type, including after naming a RES point.
   More precisely, if q is a complete RES type, then q x p^sharp is
   complete over S. This can be derived without importing HK Lemma 3.17:
   for an arbitrary definable subset of this product, generic fibre
   invariance makes membership constant on each full value fibre after
   fixing x in q; the relation saying that this fibre meets the subset is
   a RES/Gamma relation and hence a finite union of rectangles. The
   completeness of q and p then decides that relation.
3. On a full generic value fibre, a definable map from an RV m-tuple to
   an RV n-tuple is of the form c u^M with integral M and coefficients
   definable over the ground of that map. If n=m and the map is injective,
   M is unimodular. For a fixed RES point x that ground is S(x), and not
   S. The established Lean statements covering this step are in
   `RVGenericFibreMonomials.lean`.
4. The Gamma rank of a finite RV tuple over S is the rational rank of
   its tuple of values over Gamma-definable closure of S. To check this,
   use primitive integral rows and unimodular coordinate changes to
   separate all relations over the old Gamma closure. The resulting
   fixed-value coordinates form a RES tuple r; their fixed values need
   not be zero or have lifts over S. The other coordinates u have
   independent values gamma. RES parameters add no Gamma closure.
   If a Gamma point is definable from (r,u), generic fibre constancy
   makes its defining function constant on the whole value fibre of u.
   It consequently belongs to Gamma-definable closure of (S,r,gamma).
   RES/Gamma orthogonality identifies this with Gamma-definable closure
   of (S,gamma), and pure DOAG definable closure is rational linear span.
   This proves the claim. The reverse inclusion follows from taking
   values. Since a definable bijection preserves definable closure,
   this Gamma rank is invariant under such a bijection. This fact is
   needed for lower-rank remainders as well as at generic points; it is
   not a cancellation argument in a Grothendieck ring.

For clarity, the precise local conclusion from these facts is as follows.
Suppose a definable RV bijection F carries a finite union of degree-N
product objects to another such union, and m is the largest free Gamma
arity in either union. At a source point whose free Gamma tuple has full
rank m, there is a product neighbourhood X_0 x U_0^sharp on which

    F(x,u) = ( h(x), c(x) u^M ),                                (L)

in one target product chart, with

    h:X_0 -> X_1 a definable RES[N-m] bijection,
    M in GL_m(Z),
    c:X_0 -> (RV^times)^m definable,
    val(c(x))=delta in (dcl(S) cap Gamma)^m independent of x,
    F(X_0 x U_0^sharp) = X_1 x (M U_0+delta)^sharp.              (L')

Here the word neighbourhood means a definable set containing the relevant
complete type; it does not mean an open RES set. The monomial formula is
an equality for the whole product neighbourhood, not just for a chosen
angular point. The following details justify this strengthening.

First, completeness selects one target chart. Gamma rank invariance and
maximality of m force that chart to have free Gamma arity m; its RES
degree is consequently N-m. The target RES coordinate belongs to dcl(S,x).
For example, apply the rectangular generic monomial statement to its
nonzero coordinates over S(x). Their values lie in finite Gamma support.
Independence of the input Gamma tuple forces every exponent row for those
coordinates to be zero. Zero coordinates are handled by fixing their
zero pattern. The resulting output is thus a point definable over S(x).

Express that point by a partial S-definable function h of x. Product
completeness, followed by compactness, gives a product neighbourhood on
which the RES coordinate is h(x) throughout. On this neighbourhood, the
remaining RV map for each fixed x is injective: F is injective and its
RES coordinate is fixed. The square generic monomial theorem over S(x)
therefore gives a unimodular M and a tuple c in RV-definable closure of
S(x). Express c by a partial S-definable function c(x). The formula for
one such M and c holds on the complete product type; product completeness
and compactness give a smaller product neighbourhood on which it holds
throughout. No Gamma input has been named in the ground for the
coefficient theorem.

The function val(c(x)) has finite image, since X is RES. Partition and
shrink to make it the single old-ground definable tuple delta. To see
injectivity of h on the RES type, if h(x)=h(x') then the two monomial
maps at x and x' are bijections from the same full value fibre to the
same target value fibre: M is unimodular and delta is the same. Injectivity
of F forces x=x'. Compactness shrinks the RES neighbourhood so that h is
injective throughout it. Set X_1=h(X_0). Unimodularity now proves (L')
exactly, including surjectivity onto every target value fibre. Thus the
assertion used here retains, rather than descends, the RES-dependent
coefficients responsible for the obstruction.

These arguments also explain why the generic-type steps alone are not
the final exported Lean kernel theorem. The uniform neighbourhood,
finite-cover, and simultaneous scissor assembly still need formalization.

## Why these relations generate every positive equality

Work in one total degree N at a time. Each positive tensor is a finite
sum of products [X]_r tensor [U]_s with r+s=N. Each positive RV equality
is an actual definable bijection between disjoint unions of these product
objects; positive scissors are realized by actual partitions.

First normalize each Gamma factor. If U subset Gamma^s has dimension
less than s, semilinearity partitions it into pieces lying in rational
affine hyperplanes. Clear denominators and divide the normal vector by
its gcd. Complete this primitive integer row to a unimodular matrix.
The resulting integral change of coordinates writes the piece as a
subset of {a} x Gamma^(s-1), with a an old-ground definable Gamma value.
The finite Gamma factor {a} can be transferred to the RES factor by the
existing balancing relation. Its degree-one lift is a^sharp. Repeating
this process yields factors U subset Gamma^m of full dimension m,
with the RES degree increased to N-m. No unliftable translation is
performed in this normalization.

Now let F be an actual RV bijection between the normalized unions. Induct
on the largest free Gamma arity m in the two unions. When m=0 every Gamma
factor has been absorbed into RES, so F is itself a RES isomorphism and
the equality already holds in the source tensor.

For m>0 apply (L) at all full-rank types in the source charts of arity m.
Compactness gives finitely many product neighbourhoods covering these
types. The relevant partial type is the definable product together with
all inequalities e.gamma != a for nonzero integral e and a in old Gamma
definable closure. Finite Boolean refinement of the residue neighbourhoods
and the Gamma neighbourhoods makes the rectangles disjoint. Subrectangles
still have form (L), and their images in (L') are disjoint because F is
injective.

For a matched rectangle, parameter-free integral monomials already give

    [U_0]_m = [M U_0]_m

in the original Gamma category. Apply (K+) successively to the m coordinate
functions c_i:X_0 -> delta_i^sharp, to obtain

    [X_0] tensor [U_0]
      ~ [X_0] tensor [M U_0+delta]
      = [X_1] tensor [M U_0+delta].

The last equality is the RES bijection h. This is the tensor equality
needed for each matched rectangle. It uses no same-ground lift of the
translation by delta.

The remainder of each source chart has no full-rank Gamma type. Compactness
puts it over finitely many old rational affine hyperplanes. Equivalently,
use the finite RES/Gamma rectangular decomposition and observe that any
Gamma factor of dimension m would contain a full-rank type. The target
remainder has the same property by Gamma rank invariance and the inverse
of F. Subtracting the finitely many product images from the target charts
is another finite Boolean product refinement. Normalize the remainders
as above; they have free Gamma arity less than m. Apply the induction
hypothesis and assemble the equalities by positive scissors. This proves
(K+) without cancellation, division by a finite cardinal, or a change
of ground.

## Passage to the groupified kernel

Groupification of the quotient by (K+) is the quotient of the groupified
tensor by the ideal generated by the differences in (K). This algebraic
fact, including the absence of a cancellation hypothesis, is formalized
in `GroupifiedCongruences.lean`, with tensor/groupification compatibility
in `CompletionTensor.lean`.

One can also see it directly. Write a groupified kernel element as a-b,
with a,b positive. Equality of its images in the group completion means
there is a positive RV class w with Psi+(a)+w=Psi+(b)+w. Positive
surjectivity, already established locally, gives w=Psi+(t) for a positive
tensor t. The positive presentation says a+t and b+t are congruent
modulo (K+). Their difference is a-b, which lies in the ideal in (K).
The reverse inclusion was the explicit multiplication bijection above.

## A uniform annihilator, with the grading retained

Let

    tau = 1 tensor [{0}]_1 = [G_m]_1 tensor 1 in T.

This is a degree-one element, not the degree-zero unit. Then

    tau * ker(Psi) = 0.                                       (A)

Indeed put e_delta=[{delta}]_1 in the finite Gamma coefficient ring.
The function c gives a RES bijection

    X x 0^sharp -> X x delta^sharp,   (x,z) |-> (x,c(x)z).

Hence [X] tau_RES = [X] (delta^sharp)_RES. Balancing transfers that
degree-one coefficient to e_delta on the Gamma side. The integral shear

    (alpha,gamma) |-> (alpha,gamma+alpha e_i)

is an allowed GL_(m+1)(Z) map with no translation parameter. On the
slice alpha=delta it proves e_delta[U]=e_delta[U+delta e_i]. Transfer
the coefficient back to RES and use the same RES bijection in reverse.
This gives tau g(X,delta,U,i)=0 for every generator, proving (A). The same
calculation shows that multiplying a generating positive pair by tau
makes the pair equal in T+, before taking the quotient.

In particular the localized unmeasured map Psi[tau^(-1)] is an isomorphism.
This statement follows from (K), (A), and surjectivity; it does not justify
cancelling tau in the original graded ring. No claim that ker(Psi) is the
whole annihilator of tau has been established. That stronger equality
would require an additional argument about the target or the full source
annihilator, and is unnecessary for this generating presentation.

## The previously found element

For S=C((t)), delta=1/5,

    R={r:r^5=rv(t)} in RES[0], c(r)=r, U=(0,infinity),

the generator is exactly

    [R]_0 tensor ([(0,infinity)]_1-[(1/5,infinity)]_1).

The boundary detector in `TENSOR-COEFFICIENT-OBSTRUCTION.md` sends it to
-5 epsilon, so it is nonzero in T. Formula (A) kills it by one factor
of tau, not by a tacit cancellation or division by five.

This calculation is for unmeasured Psi. The same multiplication map does
not automatically preserve an RV volume form; (K) is not asserted for
the measured map mu-Psi.

## Measured companion

The author's subsequent question is answered in
`MEASURED-TENSOR-KERNEL-PRESENTATION.md`. It proves the measured analogue
with the compensating target form sigma(eta-delta e_i)-delta, gives an
explicit nonzero measured relation using the forgetful map, and retains
the degree-zero weight shifts needed in the completeness argument. The
zero-combined-weight functor embeds this unmeasured kernel into the
measured one. This follow-up does not assign the zero volume form to both
sides of the original root bijection or claim a completed Lean export.

## Euler retraction consequence

`TENSOR-KERNEL-RES-RETRACTION.md` calculates that both chi_g and chi_b
Euler evaluations annihilate this kernel, directly on its generators.
The resulting map to the graded !RES quotient therefore descends through
Psi by surjectivity, already before localization. It supplies a replacement
for the use of Psi inverse in the retraction construction, without any
additional RES quotient or a torus cancellation. This is a mathematical
descent argument, not a completed global Lean export or a certification
of every Section 4 claim.

## Witness notation and unary ring refinement

The author's follow-up correction is incorporated in the statement above:
write g(X,delta,U,i), with delta in Lambda_X, rather than indexing by a
chosen witness c. `TENSOR-KERNEL-UNARY-GENERATORS.md` further proves the
ring-ideal presentation using only
[X]_r tensor ([H_a]_1-[H_(a+delta)]_1), H_a=(a,infinity), with delta in
Lambda_X and a any old-ground definable Gamma point. Its signed cone
argument is valid after groupification; it does not by itself replace
the positive full-coordinate congruence with a unary one. The endpoint
a remains a parameter and all RES degrees remain present. Fixing the
translated coordinate to i=1 is a separate immediate simplification
valid even for the positive congruence. The complete unary argument is
not yet a Lean export.


## Actual ring-kernel exports — 2026-11-12

The positive presentations are primary. `TensorRingKernelPresentations`
now instantiates their groupification in both actual tensor products over
the original finite-Gamma coefficient rings. The ideal is the span of
`e(of a) - e(of b)` for exactly the explicit positive translation pairs
`(a,b)`, where `e` is the canonical completion/tensor equivalence. Its pure
tensor formula is checked. Thus the witness c remains existential and all
RES degrees, Gamma domains, finite tags and measured forms are retained.

`gammaGroundUnmeasuredGroupTensor_kernel` and
`gammaGroundMeasuredGroupTensor_kernel` identify these ideals with the
entire actual kernels. Both quotient ring equivalences evaluate on a
quotient class by the original groupified tensor map. The context exports
`proposition_3_18_unmeasured_ring` and `proposition_3_18_measured_ring`
retain the paper's actual VF/Gamma-generated ground.

`TensorRingDescent` proves that a ring evaluation descends if and only if
it agrees on the explicit positive pairs, and supplies the descended map,
its image formula and uniqueness. Its annular theorem identifies the full
pullback inclusion with the explicit unmeasured relation ideal, including
presentation ambiguity. The concrete bounded section 4 comparison maps
and numerical Gamma Euler constructions remain section 4 work; this is
not a claim to have constructed those maps.

These proofs follow from the already checked positive kernels and local
completion algebra. They introduce no HK, [19], R--Y or other additional
cited premise. They assume neither cancellation nor that a positive
semiring embeds in its group completion. The four new modules pass
the full integrated build and declaration audit: 1,002 supporting modules,
5,314 audited declarations and standard logical principles only.
The approved manuscript is unchanged.
