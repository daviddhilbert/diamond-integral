# Local proof campaign for Proposition 3.18

The author rejected the proposed HK inputs on November 11, 2026. Prove the
coefficient embeddings and both canonical tensor comparisons here. No HK
result is to be taken as given, and no permission question remains pending.
The former draft was moved to `.scratch/withdrawn-hk-inputs/` as historical
work; it is not a project root, accepted premise or proof dependency.

Consulted sources:

- [HK, Integration in valued fields](https://arxiv.org/pdf/math/0510133v3),
  Lemmas 3.17, 3.21–3.28 and 10.1, Proposition 10.2, Corollary 10.3,
  and Proposition 10.10(1).
- [Yin, Generalized Euler characteristic in power-bounded T-convex valued
  fields](https://arxiv.org/pdf/1509.07695v2), Section 4.2, especially
  Lemmas 4.17–4.20 and Proposition 4.21. This is a different theory; its
  cell decomposition and ordered residue field arguments are not ACVF inputs.

The proof must construct same-ground RES/Gamma product decompositions,
prove that changes of decomposition give exactly the balanced relations,
and handle the volume equations without dropping finite or degree-zero
Gamma forms. The coefficient monomorphisms require their own proof; they
are not silently inferred from tensor bijectivity.

The first local step uses the already checked ACVF finite angular exception
theorem. The set of values at which an RV set meets both a fibre and its
complement is intrinsic and finite. Away from these values membership is
constant on entire fibres. Isolating the zero value gives a residue part
with finite value support and an ordinary Gamma-fibre part. Definability
must be established over the original real/Gamma base, without naming the
auxiliary finite-exception representatives.

Further obligations: finite rectangle decomposition against finite-value
RV sets; higher-dimensional full-value-fibre/product normal forms;
full-dimensional fibre rigidity and compactness; invariance under actual
RV isomorphisms and induction on Gamma dimension; measured factorization
and graded/group-completed consequences. All remain local proof obligations.

Proposition 10.10(2) is explicitly rejected by the manuscript and is absent
from this campaign. No manuscript change is proposed by these proof steps.


Local unary progress: the same-ground mixed-fibre decomposition and finite
column partition have complete checks. Unary finite-value-support RV/Gamma
relations now have finite rectangle decompositions, including RV zero.
Gamma-valued functions on those sets have finite image and only old-ground
Gamma values. The finite-correspondence extension is also checked. These
proofs use the already checked predecessor finite-projection and ACVF fibre
strong minimality, together with proved [18] Gamma-point selection. They do
not use an HK result or import a T-convex statement into ACVF.

Unary and finite-tuple Gamma-parameter elimination now have complete
checks, including actual promoted GoodBaseGammaRelation graphs. They supply
the parameter-control ingredient for higher-dimensional orthogonality. They
are not claims of complete tensor bijectivity or coefficient injectivity.

Higher-dimensional route: the tuple elimination induction has a successful
individual check, as does the nonzero-RV-tuple version whose Gamma output
base names only the input values. Use it on finite Gamma correspondences
with RV-tuple inputs. A separate saturation argument covers entire Gamma
representative fibres by old-base finite Gamma sets and proves that an
old-base definable Gamma set contained in old-base Gamma acl is finite.
Do not claim that a chosen RV representative itself lies in acl.

For higher-dimensional RV/Gamma orthogonality, form the intrinsic boundary
of each unary Gamma column. It is first-order definable, invariant on codes,
and finite on every RV-tuple row by the proved finite-threshold theorem.
Thus it gives a GoodBaseGammaRelation. Tuple residue-parameter elimination
and Gamma algebraic finiteness make the union of all such boundaries finite.
A common finite threshold set then gives finitely many columns, and the
checked full-base Gamma-test partition provides same-ground rectangles.
This avoids replacing isolated definable atomic sets by arbitrary complete
types: [18, 3.3] alone does not justify that substitution.

After orthogonality, prove the higher-dimensional RV normal form using
integer monomial transformations and residue pieces. The tensor comparison
still requires invariance under RV isomorphisms, a decreasing Gamma-dimension
argument, and measured factorization with finite/degree-zero forms retained.


The arbitrary-tuple orthogonality extension has successful individual
checks. A nonempty full-base Gamma-tuple set has a tuple whose coordinates
are individually definable over that base. For two differing residue
columns, apply this to their symmetric difference over the base plus both
residue tuples. Two applications of the checked tuple-elimination theorem
remove those residue parameters. Saturation makes the resulting original-
ground definable separating tests finite, and finite definable column
partitioning gives disjoint rectangles over the original base. This argument
handles every finite Gamma arity and does not identify arbitrary types with
isolated definable atomic sets. Finite Gamma-to-residue correspondences then
have finite residue projection. The full 533-module build and audit pass;
these checks still do not prove the general RV product normal form or the
coefficient and tensor comparison conclusions.


RV normal-form foundations now have successful individual checks:
integer matrices with integral inverses give actual same-ground definable
monomial bijections of nonzero RV tuples, using released RV inverse and
ordinary Laurent semantics. Smith normal form places finite-value characters
in finitely many residue coordinates; torsion-free Gamma is explicit. The
source guarded equality splits by the two outer values. Unequal values
force both residue-polynomial factors to vanish, while equal values retain
the actual residue ratio. Absorbing zero and flat-sum domain guards are kept.
These are foundations for the geometric product normal form, not a proof
of that normal form or of Proposition 3.18.


The 559-module build and audit pass (1799 public theorem types, 3667
audited heads). Guarded clause covers and their free-value angular
invariance are proved. A global value-pattern refinement is being checked
to obtain a disjoint partition before positive scissor assembly. Its
internal total flat-sum congruence keeps the exact released junk-zero
semantics; the actual formula still contains all pole and residue guards.
A further original-ground descent lemma removes the proof-only common RV
representatives from Gamma definable closure. See LOCAL-RV-NORMAL-FORM.md
for the open geometric assembly and isomorphism-invariance obligations.


The **580-module** project build and full audit pass with **1869** public
theorem types. The actual same-real-ground finite angular partition theorem
now preserves the source parameter package and all guarded-DNF domain
certificates. Its cells are definable, pairwise disjoint and cover every
nonzero RV tuple in the set. Each cell has proved integral monomial angular
data with finite residue-coordinate values. The semantic coordinate
quotient and nonzero RV presentation are checked. The latest section 2
regression passes (850 public theorem audits and 378 reuse audits).
Actual product maps, original-Gamma-ground assembly, finite-to-one label
transport, coefficient injectivity and tensor invariance remain open.


The **601-module** project build and full audit pass: **1937** public
theorem types, **1769** definitions, **151** named instances and **8**
selected reused declarations (**3865** audited heads). The local geometric
normal form now constructs finite disjoint definable pieces on a nonzero
RV tuple locus, actual residue and Gamma factors, and same-real-ground
definable product bijections. The residue factors have finite Gamma support
and the Gamma factors use their entire RV value preimage. Actual ambient
arities add to the input ambient arity; RV[k] label degrees are not inferred
from those arities. The original-real/Gamma-ground angular partition and
coefficient-value descent are also checked. General product assembly at
that ground, label/degree transport, generic torus rigidity, coefficient
injectivity and both tensor bijections remain local proof obligations.
No HK premise or manuscript edit is introduced.


The **613-module** project build and full audit pass with **1963** public
theorem types, **1783** definitions, **151** named instances and **8**
selected reused declarations (**3905** audited heads). The actual finite
geometric product normal form is now proved over the original real/Gamma
ground: all source pieces, residue and Gamma factors, and product
bijections retain that ground and every RV code of each Gamma fibre.
The hypotheses explicitly include small real and Gamma bases, saturation,
ACVF00, canonical structure and a nontrivial Gamma value definable over
the original mixed ground. There is no stronger real-base nontriviality
assumption. The theorem currently covers the nonzero RV tuple locus and
records ambient product arities; RV[k] degree transport, zero-coordinate
assembly, isomorphism invariance, coefficient injectivity and both tensor
bijections remain separate local obligations. No HK input is used.


The **623-module** project build and full audit pass with **1978** public
theorem types, **1796** definitions, **151** named instances and **8**
selected reused declarations (**3933** audited heads). The geometric
normal form now covers the entire original RV tuple domain, including all
zero coordinates, by injective parameter-free nonzero coding followed by
pullback of the product charts. Algebraically independent lifts in full
Gamma fibres give the rank bound rank(residue point) + Gamma arity ≤ RV[k]
label degree. A finite-value-support residue set with that rank bound has
an actual same-ground RES[k-m] representative with a nonzero finite-to-one
label. The full Gamma fibre is also bijective with the literal Gamma/RV
code lift. Later tensor-chart and finite-partition assembly is outside this
receipt. Coefficient injectivity, tensor injectivity and measured tensor
comparison remain local obligations; no HK result is assumed.


The corrected **631-module** project build and complete audit pass:
**1992** public theorem types, **1802** definitions, **151** named instances
and **8** selected reused declarations (**3953** audited heads). This
receipt includes local surjectivity of the actual unmeasured positive
balanced tensor map and of its group-completed map over the original
real/Gamma base. The proof uses full-domain product normal form, actual
RES label-degree transport, literal full Gamma fibre lifts and finite
positive-scissor assembly. All needed earlier exchange/Gamma algebraicity
records are supplied by checked [18] adapters; no HK premise is present.
An earlier attempted build detected a helper-file name collision. The
legacy `GammaGroundBijection.ofEmpty` public helper was restored, and the
new empty-class lemmas were moved to `GammaGroundRVEmptyClasses.lean`.
The complete rebuild and audit then passed, including its affected ordinary,
measured and Gamma-lift dependents. Tensor injectivity, coefficient
embeddings and the measured tensor comparison remain open.


The **641-module** full project build and audit pass: **2014** public
theorem types, **1811** definitions, **151** named instances and **8**
selected reused declarations (**3984** audited heads). The new local
Gamma-valued RV function theorem covers the graph by finitely many total
Gamma functions over the original base. It removes angular RV names from
Gamma definable closure, abstracts finite Gamma parameters using universal
full-code predicates, functionalizes the resulting graphs and applies
actual saturation. The actual volume-map adapter and finite Boolean
refinement give pairwise disjoint original-ground source cells, each with
one such Gamma function of its coordinate values. No definable Gamma
section or HK premise is used. Unmeasured positive/group tensor surjectivity
remains proved; injectivity and the measured tensor comparison remain open.
The next adapters expose the monomial value-reconstruction formula and
partition residue factors by finite individually definable value tuples.


### Local measured product geometry — 655-module checkpoint

The full build and principle audit pass: 2034 public theorem types,
1819 printed definitions, 151 named instances and 8 selected reused
heads (4012 audited heads). Only the standard logical principles occur.
`GammaGroundRV_form_normal_form` now proves finite disjoint product
charts for every actual original-ground definable Gamma-valued weight
on a full RV tuple domain, including zeros. The charts retain an explicit
original-ground Gamma function giving the weight on the Gamma factor.
The proof reconstructs original values by the integral inverse monomial
matrix and splits the finite residue-value support into individually
original-ground definable Gamma tuples. It adds no RV representatives
to the ground and uses no HK input.

This is the measured geometric decomposition, not the measured tensor
comparison: the actual RES label degree, volume-form allocation and
positive scissors assembly still need to be joined to these charts.
The coefficient monomorphisms and tensor injectivity remain open.


### Concrete measured tensor surjectivity — 663-module checkpoint

The full build and audit pass: 2052 public theorem types,
1829 definitions, 151 named instances and
8 selected reused heads (4040 audited heads), using only the
standard logical principles. `MeasuredTensorSurjectivity` proves actual
object preimages and surjectivity of both `gammaGroundMeasuredTensorMap`
and `gammaGroundMeasuredGroupTensorMap`. It uses the locally proved
form-product charts, actual RES[k-m] degree transport, prescribed combined
weights converted to genuine same-ground volume forms, and finite positive
scissors assembly. Finite and degree-zero Gamma forms are retained.
No HK premise is used. Both unmeasured tensor surjectivity results remain
checked. Tensor injectivity and the Gamma-to-RV coefficient monomorphisms
remain open; Proposition 3.18 is not yet complete.


### Generic value fibres — 672-module checkpoint

The full build and audit pass: 2066 public theorem types,
1836 definitions, 151 named instances and 8 reused heads
(4061 audited heads), with standard principles only.
`GammaGenericValueFibres` proves original-ground generic value-fibre
invariance and constancy of actual Gamma-valued maps. `ResidueGenericValueFibres`
proves the version after naming a residue point and constancy of actual
maps into finite-value-support residue sets. `RVProductGenericMaps`
retains these statements after fixing a residue input in a product chart.
`RVFullGammaFibreDegree` proves that any finite-to-one map from a nonempty
full Gamma-preimage of arity m into RV[k] forces m ≤ k. The statements
about generic tuples are conditional geometric lemmas; they do not claim
existence or density of such tuples. Both tensor surjectivity proofs remain
checked. Injectivity and the coefficient monomorphisms are still open.


### Full-fibre monomial rigidity — 680-module checkpoint

The full build and audit pass: 2091 public theorem types,
1841 definitions, 151 named instances and 8 reused heads
(4091 audited heads), with standard logical principles only.
`RVMonomialFibreRigidity.rvMonomial_full_fibre_unimodular` and its affine
version prove that injectivity of an integral monomial map on one complete
RV value fibre forces a unit determinant. `FieldUnitPowerKernels` proves
the necessary characteristic-zero root-of-unity obstruction, and
`RVResiduePowerKernels` constructs the embedding of the actual algebraically
closed residue-field units into actual RV units, proves its value is one,
and derives the power-kernel obstruction without any HK premise.
`RVAngularInverseMonomials` retains the actual inverse chart formula, and
`RVAngularGraphRigidity` applies full-fibre rigidity to a square free input
block of an angular graph chart. The source projection remains injective
on the original graph. The matching-arity hypothesis is explicit; its
consequence at generic points and tensor invariance still need proof.
Both tensor surjectivity results remain checked. Neither tensor injectivity
nor the Gamma-to-RV monomorphisms are claimed complete.


### Generic graph arities and coefficients — 695-module checkpoint

The full build and audit pass: 2113 public theorem types,
1844 definitions, 151 named instances and 8 reused heads
(4116 audited heads), using only standard logical principles.
`RVAngularLabelDegree` proves that the free arity of an angular cell at a
Gamma-generic k-coordinate input equals its actual RV[k] label degree.
`RVGenericGraphBlocks` therefore supplies a square unimodular input block
without assuming matching arity. The lower bound uses the proved integral
left-kernel lemma for rectangular matrices and the old-ground Gamma values
of the residue coefficients. `RVAngularResidueUniqueness` proves that a
fixed residue-value fibre of an injective square product chart is a
singleton. `GammaGroundAngularResiduePoints` constructs actual original-
ground definable singleton pieces, and `GammaGroundAngularCoefficientPoints`
proves original-ground RV definability of the actual inverse-chart
coefficients and their definable images. Rectangular monomial maps retain
their parameter-free code graphs in `RVUnitRectangularMonomials`.

These are local graph results, not yet a complete classification of all
Gamma morphisms or tensor injectivity. Both tensor maps and their group
completions remain proved surjective. Finite-Gamma/residue-torus matching,
finite coefficient descent and lower-free-arity induction remain separate
obligations. The manuscript has not changed.


### Actual unit graphs and output formulas — 703-module checkpoint

The full build and audit pass: 2128 public theorem types,
1856 definitions, 151 named instances and 8 reused heads
(4143 audited heads), using standard principles only.
`GammaGroundRVUnitGraphs` presents actual definable-map graphs as unit
RV tuples, proves injectivity of their input projection (and output
projection for injective maps), and constructs an actual finite input
label. `RVProductResidueFinite` proves finiteness of a residue factor
when the full Gamma factor exhausts the label degree. Integral block
elimination is proved in `IntegerMonomialElimination`;
`GammaGroundAngularOutputMonomials` gives graph outputs as integral
monomials in the original input with actual old-ground RV coefficients.
`RVAngularOutputRigidity` proves unimodularity of the induced output
matrix when both projections are injective. Tensor injectivity and the
Gamma coefficient monomorphisms remain open; finite-Gamma/residue-torus
matching and descent must still be handled. Both surjectivity results
remain checked. No manuscript change or HK premise has been introduced.


## Generic-fibre monomials and critical review — 2026-11-12

The integrated build and complete audit pass for 712 supporting modules
plus their aggregate: 2142 public theorem types, 1860 definitions, 151
named instances and 8 reused declarations (4161 audited heads), with only
standard logical principles. `RVGenericFibreMonomials` proves an actual
old-ground definable RV map is an integral affine monomial on the entire
value fibre of a Gamma-independent input, with individually old-ground
RV-definable coefficients. For an injective square map its matrix is
unimodular. `UnimodularMonomialFibres` and `RVAngularInputFibres` supply the
whole-fibre solution argument. `GammaGroundUnitFibreDescent` and
`GammaGroundMonomialFibreDescent` construct actual Gamma morphisms,
including full code lifts, from value-kernel-preserving RV bijections.

A critical obstruction to the remaining tensor injectivity was found while
checking finite coefficient descent. Over S=C((t)), the five RV roots R of
rv(t) supply a coefficient-dependent translation between the full lifts
of (0,infinity) and (1/5,infinity). Thus the two corresponding R-weighted
RV products are isomorphic. A periodic odd endpoint-weight invariant,
extended through the tensor universal property to Z[epsilon]/(epsilon^2),
distinguishes their source tensors. The full mathematical argument and its
scope checks are in `verification/TENSOR-COEFFICIENT-OBSTRUCTION.md`; the
concrete model and complete detector are not yet Lean constructions.
This is not a claim that the measured map has the same counterexample.

Review item T001 presents this argument in blue beside Proposition 3.18
in a manuscript copy, at
`reference/proposed-revisions/T001-finite-coefficient-review.pdf`, printed
pages 34–35. The PDF-only right-panel request returned queued. The working
manuscript is unchanged. The author must review the mathematical obstruction
before a replacement theorem or change of ground/coefficient conventions
is chosen. No new HK acceptance request is pending; no HK premise was used.
Both positive tensor surjectivities and their group completions remain
proved. Neither tensor injectivity nor the coefficient monomorphisms are
claimed complete, and section 3 remains unfinished.


## Thorough HK convention audit — 2026-11-12

At the author's request, the parameter, algebraic base-change, RES,
Gamma-morphism, effective/resolved, grading and localization conventions
were traced through HK and the full tensor argument. Critical passages
were compared in arXiv v2/v3 and cached text of Oxford's accepted manuscript.
The publisher's full typeset chapter was not accessible. The source map,
rejected possible resolutions, and independent balancing calculation are
recorded in `verification/HK-CONVENTION-AUDIT.md`.

No convention was found that resolves T001 for the fixed-ground,
unlocalized graded tensor. The example satisfies tau*a=tau*b, where tau
is the degree-one finite-Gamma singleton whose RV lift is the residue
torus. It therefore vanishes after tau-localization, but the stated
Corollary 10.3 tensor is not localized. This is a concrete explanation
of why the separate localized constructions do not establish its original
injectivity. Merely replacing the translation subgroup by its divisible
hull would instead invalidate the fixed-ground RV lift of a singleton.
No main-text correction or replacement theorem is adopted. The Lean
sources and verification receipt are unchanged; T001 remains open for
mathematical review, and no complete Lean counterexample is claimed.


## Claim 3: the exact strength needed for induction

The finite-root example satisfies Claim 3's stated product and fibre
conclusions, with RES map h(r)=r and Gamma map k(gamma)=gamma+1/5.
Thus the diagnosis is that the stated claim is too weak for the tensor
identification; it is not refuted by that example as a statement about
definable factor bijections. Fixing r gives a lift over S(r), not S.

The stronger same-ground-lift conclusion is false even after shrinking
around the Gamma type at positive infinity. Every definable neighbourhood
of that type contains a tail and hence an integer N. A lift over S=C((t))
evaluated at rv(t)^N would give an S-definable RV element of value N+1/5,
contradicting RV definable closure over this henselian ground. This rules
out every possible same-ground lift on those neighbourhoods, not just the
particular multiplication-by-r formula. The complete line-by-line audit
and corrected weak/strong distinction are in `verification/HK-CLAIM3-AUDIT.md`.
The supporting Lean sources and approved manuscript are unchanged.

## Follow-up kernel calculation

`TENSOR-KERNEL-PRESENTATION.md` gives the mathematical presentation of the
unmeasured kernel by RES-dependent coordinate translations, including the
reverse-inclusion argument and a single degree-one torus annihilator.
This replaces neither a missing local proof with HK input nor the original
author-reviewed statement with an unapproved theorem. The full kernel
equality is not yet exported in Lean; the current colored T001 PDF is
`../reference/proposed-revisions/T001-kernel-review.pdf`.

## Measured follow-up

`MEASURED-TENSOR-KERNEL-PRESENTATION.md` supplies the corrected measured
generators, with sigma_delta(eta)=sigma(eta-delta e_i)-delta, and a full
mathematical completeness argument retaining the shared degree-zero
weight-shift coefficients. The fifth-root relation is nonzero by the
forgetful map to the ordinary tensor. Both kernels have a degree-one
torus annihilator. No HK premise has been introduced; the complete
geometric kernel theorem is not yet a Lean export. The current colored
PDF is `../reference/proposed-revisions/T001-measured-kernel-review.pdf`.

## Euler retraction consequence

The unmeasured kernel generators are killed by both Euler evaluations
into the existing !RES quotient. Hence the retraction formulas descend
through the surjective Psi without using injectivity or Psi inverse.
`TENSOR-KERNEL-RES-RETRACTION.md` records the balancing and vanishing
calculations, before localization, and their formalization boundary.
No new HK input, cancellation of a torus class, or extra quotient of RES
is used. The current one-item colored PDF is
`../reference/proposed-revisions/T001-retraction-review.pdf`.

## Author correction and unary ring presentation

The witness c is now existential and the generator is indexed by delta
in Lambda_X. `TENSOR-KERNEL-UNARY-GENERATORS.md` proves a further
unmeasured ring-ideal presentation by unary open-ray differences, using
a signed translation-compatible cone expansion and integral cone
refinement. This is additional polyhedral formalization work, not an
accepted HK theorem or a completed Lean export. The proof retains all
affine endpoints and does not assert a unary positive congruence or a
measured unary refinement. The current colored review is
`../reference/proposed-revisions/T001-unary-generators-review.pdf`.

## Finite coefficients and the P_Gamma priority check

The finite-only coefficient restriction is ruled out mathematically by
`TENSOR-KERNEL-FINITE-COEFFICIENTS.md`; the author's acknowledgment does
not establish minimality of every individual coefficient. The subsequent
priority check in `P-GAMMA-PULLBACK.md` proves the full natural pullback
lands in the unmeasured kernel after forgetting forms, because each
stipulated P_gamma vanishes in the full unmeasured ring by an actual
old-ground tail bijection. This argument does not use HK or full tensor
kernel generation. It proves RES-retraction descent while retaining the
extra bounded tensor kernel in the correct quotient presentation. The
canonical annular lifts alone do not absorb that kernel. All these
concrete detector and descent statements remain mathematical proofs,
not complete Lean exports. The current colored PDF is
`../reference/proposed-revisions/T001-p-gamma-pullback-review.pdf`.
