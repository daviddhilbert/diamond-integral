# T001: the witness is existential, and unary rays generate the ring kernel

This addresses the author's two corrections to the notation and size of
the unmeasured generating family. The function c is a witness, not an
extra dependence of a fixed displayed difference. Moreover the kernel
ideal after groupification can be generated with one Gamma variable.
This second assertion uses an additional signed polyhedral argument;
it does not by itself give a unary positive-semiring congruence.

## Correct the indexing

For an actual RES[r] object X, let

    Lambda_X = {delta in Gamma cap dcl(S) :
                  there exists an S-definable c:X -> delta^sharp}.

The element formerly written g(X,c,U,i) is better written

    g(X,delta,U,i) = [X]_r tensor ([U]_m-[U+delta e_i]_m).

For delta in Lambda_X, choose a witness c only to construct the RV
bijection proving that this element is in ker(Psi). A different witness
with the same constant value delta leaves the displayed element
unchanged. Existence is a sufficient condition for including this
generator; it is not asserted to be a necessary condition for every
individual such difference to vanish for other reasons.

For nonempty X, Lambda_X is a subgroup: witnesses for sums and negatives
are products and inverses. In particular, a witness c for delta supplies
c^n for every integer multiple n*delta. The empty-X case contributes
only zero generators.

## A unary ray presentation of the groupified kernel

Let H_a=(a,infinity) in Gamma[1], with a any S-definable Gamma point.
Then the groupified unmeasured kernel has the presentation

    ker(Psi) = ( [X]_r tensor ([H_a]_1-[H_(a+delta)]_1) :
                    X in RES[r], a in Gamma cap dcl(S),
                    delta in Lambda_X ).                    (U)

Thus no coordinate index i or higher-arity Gamma object U is needed for
this ideal presentation. Every displayed generator has degree r+1.
The endpoint a is allowed to vary; no reduction to the single fixed
ray H_0 is used. The original fifth-root diagnostic is a=0, delta=1/5.
All RES degrees r remain present; X has not been restricted to finite
objects.

There are two distinct reductions. Merely fixing the translated
coordinate to i=1 is immediate by a parameter-free coordinate permutation
and is also valid before groupification. Restricting the entire Gamma
factor to one variable, as in (U), is stronger and requires the argument
below.

## Translation-compatible cone expansion

We need the following elementary polyhedral statement in its equivariant
form, not just abstract generation of a Grothendieck ring.

For every definable semilinear U subset Gamma^m, its indicator is a finite
integer combination of indicators of affine cones v_j+C_j, where:

* v_j belongs to (Gamma cap dcl(S))^m;
* C_j has rational directions;
* after a matrix M_j in GL_m(Z), the affine cone becomes a product of
  unary sets, each a whole Gamma line, a closed ray [b,infinity), or a
  singleton {b}.

The same signed expansion for U+d is obtained by replacing every v_j
with v_j+d, keeping the cones, matrices and coefficients fixed. In the
product coordinates, the endpoints consequently shift by M_j*d. No
translation by v_j is asserted to be an allowed original-ground Gamma
morphism: the affine endpoints are retained as parameters in the unary
objects.

Here is a construction of this expansion.

1. Boolean combinations of rational affine inequalities reduce by
   scissors and inclusion-exclusion to closed polyhedra. Split rational
   lineality by a unimodular change of coordinates. Affine hull equations
   similarly give fixed Gamma coordinates; all affine constants remain
   old-ground definable, without choosing RV lifts.
2. In the remaining line-free polyhedron, the finite Brianchon--Gram
   indicator identity expresses the polyhedron as the alternating sum
   of tangent cones along its bounded faces. This is the finite Euler
   relation on faces, checked pointwise using the visible-face complex.
   A tangent cone can be based at any definable vertex of its face.
   Lifting the separated lineality gives affine cones in the original
   ambient degree m. The line-free qualification matters: one must not
   apply the bounded-face formula directly to a polyhedron with lines.
3. Triangulate each pointed rational cone into simplicial cones, with
   lower-dimensional intersection terms included by scissors. A
   simplicial lattice cone of index D>1 has a nonzero lattice point in
   its fundamental parallelepiped. Subdivision along its primitive ray
   gives maximal subcones of smaller positive index. Induction on
   dimension and index expresses the original cone as an integer
   combination of unimodular cones and their faces. The rational
   lineality lattice is saturated and can be extended to an integral
   basis, so each resulting cone is an integral-basis product of rays,
   lines and points.

All these subdivisions are in the direction cones, so translating the
apex leaves them unchanged. Indicator identities give actual additive
scissor identities in K Gamma[m], with ambient degree m throughout.
For arbitrary divisible ordered Gamma, the construction is valid
casewise by DOAG quantifier elimination: the finite face pattern,
rational formulas for vertices, and indicator identities are determined
by finitely many rational linear comparisons of the parameters. Each
such case is a first-order polyhedral identity already valid over the
real ordered group. This does not assume that Gamma is Archimedean.

This is a separate mathematical proof step, not a new accepted HK input
or an existing Lean export. For the line-free bounded-face identity,
a useful proof reference is Derksen--Fink, *Valuative invariants for
polymatroids*, Section 4, Theorem 4.1:
https://sites.lsa.umich.edu/hderksen/wp-content/uploads/sites/614/2018/05/A.I.a.33.pdf
The identity and the elementary lattice-cone subdivision still require
local formalization for a fully checked unary presentation.

## Reduce the higher-dimensional translation generators

Let J be the ideal on the right of (U). Certainly J lies in ker(Psi),
by the explicit RV multiplication bijection using a witness for delta.
To prove the reverse inclusion, use the previously derived full-arity
kernel presentation and take

    [X]_r tensor ([U]_m-[U+delta e_i]_m), delta in Lambda_X.

Apply the same cone expansion to U and its translate. After each allowed
linear change M_j, we must compare two products of m unary factors,
whose corresponding endpoints differ by integers n_k*delta. Each such
shift is admissible for the same X, because c^(n_k) is a witness.

For products use the telescoping identity

    product a_k - product b_k
      = sum_k (product_(j<k) b_j) (a_k-b_k) (product_(j>k) a_j).

Multiplying the whole identity by the RES coefficient [X] keeps that
same coefficient on each unary difference; the other factors are
ordinary Gamma multipliers of degree m-1 in the tensor ring.

* A whole-line factor is unchanged by translation.
* A singleton difference already vanishes after multiplying by [X].
  Indeed c^n gives the RES bijection
  X x a^sharp -> X x (a+n*delta)^sharp. Finite-Gamma balancing identifies
  the two tensor expressions. This uses degree-one value fibres and
  does not cancel them.
* A closed-ray difference equals its open-ray difference plus the
  corresponding singleton difference. The open-ray term belongs to J
  by (U), and the singleton term is zero by the preceding bullet.

Every term of the translated cone expansion therefore belongs to J.
The full-arity kernel generators lie in J, proving (U). Total degree
is r+m throughout the reduction: a unary generator of degree r+1 is
multiplied by Gamma factors of degree m-1. No torus localization,
division by a finite cardinal, or enlargement of the ground is used.

## Positive and measured scope

The cone expansion uses negative integer coefficients. Accordingly (U)
is proved here for the kernel ideal after groupification. It is not
automatically a unary generating presentation of the positive semiring
kernel congruence, for which the earlier full-coordinate family remains
the recorded presentation. Fixing i=1 by coordinate permutation is
valid at that positive level too.

The analogous notation correction in the measured note is incorporated:
the measured generator is indexed by delta, and existence of c is its
admissibility condition. No unary reduction of the measured generating
family is claimed by this unmeasured cone argument; its volume forms
would also have to be tracked through that refinement.

The approved working manuscript, Lean sources and audit receipt are
unchanged. Earlier PDFs are preserved as review history; the current
colored T001 review displays the existential condition and (U).

## Finite-coefficient follow-up

`TENSOR-KERNEL-FINITE-COEFFICIENTS.md` now rules out the proposed
restriction to finite RES[0] coefficients by a connected genus-two
RES[1] example and a balanced tensor detector. The proof separates its
degree-two kernel element from the ideal of all finite-coefficient
translation relations, including arbitrary Gamma arities. This requires
positive-dimensional coefficients but does not prove that every
individual X is indispensable or that the whole family is minimal.
