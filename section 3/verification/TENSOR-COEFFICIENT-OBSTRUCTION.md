# T001: finite RV coefficients obstruct the stated tensor injectivity

Date: 2026-11-12. Status: critical mathematical review, awaiting the author's
reading and comments. This is a mathematical counterexample argument, not
a claim that a concrete Laurent-series model and the complete boundary
invariant have already been constructed in Lean.

The working manuscript is unchanged, at SHA256
`7dc1818a674a975ae970d376f2c487d7ab6f225392e1b316e478d10cb1cb6492`.
The colored proposal is inside a copy of the manuscript, beside Proposition
3.18, in `../reference/proposed-revisions/T001-finite-coefficient-review.pdf`.
The focused extract includes printed pages 34–35. Only that PDF was requested
in the right panel. The app returned `queued`; visibility was not confirmed.
There is no corresponding referee item to gray out.

## Scope checked independently

The standing convention allows an arbitrary parameter substructure with
nontrivial Gamma(S). Definition 3.13 uses Gamma morphisms that lift over the
original ground. Remark 3.15 retains the restriction that integral-affine
translation constants be values of original-ground definable RV elements.
The proposed example is already VF-generated and henselian, so it does not
rely on extending the accepted [19] classification to arbitrary mixed bases.
The real field being nontrivially valued is stronger than the standing
nontrivial Gamma assumption and is satisfied in this example.

## RV equality

Take S = C((t)), embedded as a small valued subfield of the saturated
ACVF(0,0) universe, and normalize v(t)=1. The definable RV values over this
henselian ground are Z; the definable Gamma points are its divisible hull Q.
Let delta=1/5, R={r in RV : r^5=rv(t)}, I=(0,infinity), J=(delta,infinity).
The set R has five elements, all of value delta, and is an actual RES[0]
object: its label is the finite map to RV^0. Its elements are not individually
S-definable. The map (r,x) -> (r,r*x) is S-definable from R x I^sharp onto
R x J^sharp, with inverse (r,y) -> (r,r^(-1)*y). Both products are RV[1]
objects with finite labels given by their second coordinates. RV morphisms
ignore compatibility with those labels, so this is a valid RV[1] morphism.
Thus Psi sends a=[R]_0 tensor [I]_1 and b=[R]_0 tensor [J]_1 to the same
class. No extra RV root was named.

## A detector on the tensor source

Define F:Q -> Z by F(q)=1 if q belongs to 1/5+Z, F(q)=-1 if q belongs to
-1/5+Z, and F(q)=0 otherwise. These two cosets are distinct. Put
F(-infinity)=F(infinity)=0. The function is odd and Z-periodic.

For an interval with endpoints c<d, assign weight F(c)-F(d), regardless of
whether each finite endpoint is included. Assign points weight zero. Extend
by addition to a finite interval/point decomposition of a unary definable
Gamma set. Such decompositions have rational finite endpoints over S.
The result nu is independent of decomposition: each subdivision at e uses
(F(c)-F(e))+(F(e)-F(d))=F(c)-F(d), and adding or deleting endpoints changes
only points, whose weight is zero. Any two decompositions have a common
refinement by their finitely many endpoints.

Translations by z in Z preserve nu by periodicity. Reflection followed by
an integer translation preserves nu because
F(-d+z)-F(-c+z)=F(c)-F(d); the same calculation applies to rays using the
chosen infinite endpoint values. By Remark 3.15, each Gamma[1] morphism is
piecewise one of these maps over S. Additivity over its finite definable
partition therefore proves isomorphism invariance. Tagged disjoint unions
are treated additively. In particular nu(I)=0, nu(J)=1, and nu vanishes on
all finite Gamma[1] objects.

Let D=Z[epsilon]/(epsilon^2), with degree zero Z, degree one Z*epsilon, and
all higher degrees zero. Define two graded semiring homomorphisms:

* RES[*] -> D: cardinality in degree zero, zero in every positive degree.
  Every degree-zero RES object is finite. Cardinality respects its
  isomorphisms, scissors, and products. Positive-degree products remain in
  positive degree, which proves multiplicativity in all remaining cases.
* Gamma[*] -> D: cardinality in degree zero, nu(X)*epsilon in degree one,
  and zero in degree at least two. Degree-zero multiplication is disjoint
  repetition. Products of two positive-degree classes have degree at least
  two and map to zero, as does their product in D, since epsilon^2=0.

Both send every positive-degree finite Gamma class to zero and every
finite degree-zero class to its cardinality. They therefore agree on the
entire finite-Gamma coefficient semiring, including its products and sums.
The universal property of the actual semiring tensor gives a detector
from its source to D. It sends a to 0 and b to 5*epsilon, which is nonzero.
This proves a != b. Since D is a ring, the same detector extends to additive
group completion and proves the difference remains nonzero there.

This checks the balancing issue directly; it does not infer tensor
inequality merely from the absence of an unweighted Gamma isomorphism.
It uses neither cancellation by a residue-torus class nor division by |R|.

## Consequence and review boundary

With the manuscript's present graded finite-map RV categories and same-ground
Gamma lifts, unmeasured tensor injectivity in Proposition 3.18 fails. The
example already rules out the combined isomorphism assertion; it does not
assert a separate counterexample to the measured tensor map. In particular,
the unmeasured example must not be silently given zero weights and called
measured: multiplication by r changes the combined value weight by delta.

The local proofs of both tensor surjectivities and their group-completed
versions remain valid. The generic-fibre monomial theorem also remains
valid: its coefficients are definable over the fixed base of the map. In
the example, after fixing r that base has been enlarged, and the coefficient
r cannot be descended to S. This is precisely the step the construction
must not assume.

The colored proposal asks the author to review the obstruction before
choosing a replacement theorem or changing the ground/coefficient
conventions. Adding a divisibility/splitting hypothesis would exclude this
example but has not been proved here sufficient for every remaining claim
and could affect the paper's intended Laurent-series applications. Enlarging
Gamma morphisms alone is not a verified repair: a Gamma translation without
a same-ground RV lift would undermine the claimed Gamma-to-RV functor.
No such repair has been incorporated or assumed.

No HK result has been imported as a premise. HK and arXiv:1509.07695 §4.2
remain proof references only; neither replaces the original-ground descent
obligation above.


## Clarification in response to the author's question

The phrase “until the intended ground or coefficient conventions are
corrected” was premature and is withdrawn. No sufficient replacement
hypothesis or modified tensor presentation has been proved. “Ground” meant
keeping S fixed versus adjoining RV representatives of definable values;
“coefficients” meant the tensor's finite-Gamma balancing relations versus
relations that also account for families depending on finite RES parameters.
These are possible places to investigate, not identified errors or approved
changes to the paper's conventions.

This objection cannot be presented as only a mismatch in diamond-integral.
The checked arXiv HK text, math/0510133v3, Definition 3.66 has the relevant
finite-label RV and finite-value RES categories; Definition 9.1 explicitly
allows a nondivisible translation subgroup. The step under scrutiny is the
transition from definable factor bijections in Proposition 10.2, Claim 3,
to the equality of tensor terms near the end of that proof. A definable
Gamma bijection must additionally have a same-ground RV lift to give an
allowed Gamma morphism. A lift over S(r), supplied by fixing a residual
coefficient r, cannot be treated as a lift over S without proof. This is
the specific apparent gap. If the example meets HK's intended identification
of the Gamma translation subgroup with the RV base, it challenges HK's
injectivity argument in that generality too. This is not a conclusion about
all of HK integration, nor a separately demonstrated failure of the measured
comparison. The concrete counterexample remains a mathematical review
argument, not a complete kernel-checked Laurent-series construction.

Source consulted directly: https://arxiv.org/pdf/math/0510133v3,
Definitions 3.66 and 9.1, §10.1, Proposition 10.2 (Claim 3 and the final
inductive step), and Corollary 10.3. An Oxford repository copy could not be
fetched (HTTP 403); no independent published-text comparison is claimed.


## Follow-up convention audit

The author requested a thorough HK convention check. The completed source
and mathematical audit is `HK-CONVENTION-AUDIT.md`. It recovered readable
cached text of the Oxford accepted manuscript after the earlier direct
403 and compared the relevant passages with arXiv v2/v3. The audit found
no resolving blanket convention. It also derives tau*a=tau*b explicitly;
this explains why tau-localization removes the example while ordinary
additive group completion and the unlocalized graded tensor do not.
The previous note about the Oxford copy being unavailable describes the
earlier direct retrieval, not the later cached-text access.

## Follow-up: a generating presentation

At the author's request, `TENSOR-KERNEL-PRESENTATION.md` now calculates the
unmeasured kernel mathematically by all RES-dependent coordinate
translations. The finite-root element is one such generator. The positive
congruence and its groupified ideal, the reverse inclusion via local
monomial rectangles, and the single degree-one torus annihilator are
spelled out there. Its global completeness proof is not yet a Lean
export. The current one-item T001 manuscript-context PDF is
`../reference/proposed-revisions/T001-kernel-review.pdf`; no replacement
statement has been incorporated into the approved working manuscript.

## Measured follow-up

The subsequent calculation in `MEASURED-TENSOR-KERNEL-PRESENTATION.md`
does produce a measured counterexample, with the form on J equal to
-1/5 while the form on I is zero. The Gamma-Jacobian of the root
multiplication is 1/5, so this precise choice is measured. Forgetting
forms proves that its tensor difference is nonzero. The earlier warning
against simply assigning zero forms to both products remains relevant.
The complete measured kernel presentation and its mathematical proof
are recorded in that companion note; full Lean completion is not claimed.
