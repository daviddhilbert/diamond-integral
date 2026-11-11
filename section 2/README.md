# Section 2 — Technicalities

Annotated manuscript, beginning on p. 10.

All tracked numbered §2 targets are now implemented in the exact scopes in
[COVERAGE.md](COVERAGE.md). Final audit: **850 public section theorems and
378 selected reuse declarations**, PASS, with nine explicit accepted cited
inputs and only the three standard logical principles. The final extensions
of 2.25–2.26, 2.29 and 2.30 retain existing finite DC ground names. See the
[proof review](verification/DISC-GROUND-REVIEW.md) and
[machine record](verification/status.json). No manuscript approval remains
pending; all 30 §2 annotations are resolved.

§2.1 reuses the pinned ACVF syntax, VF/RV carriers, genuine Gamma quotient,
parameter bases and disc codes. `Section.lean` exports the conventions,
RV-hull laws, uniform disc maps and composition with intermediate RV labels.

The author has resolved R022–R024; see [STATUS.md](STATUS.md) for the exact
interpretations and the finite-open-radius correction to the companion library.
The [review PDF](reference/section2-resolved-review.pdf) retains the original
referee text in gray and adds brief author resolutions in green.

Run `python3 'section 2/prepare-reuse.py'`, then
`lake env python3 'section 2/verify.py'` from the project root with the pinned
toolchain activated. Verification records state their actual coverage.

## Implementation history

Earlier counts and unfinished-work notes below record past milestones; the
current scope inventory above supersedes them.

Lemmas 2.11–2.15 are implemented in the precise scopes in `STATUS.md`.
`Bases.lean` gives the field and
RV-representative interface without assuming definable closedness.
`Henselianity.lean` and `AlgebraicEnvelope.lean` prove both directions of
2.11 in the canonical encoding of the two-sorted language. `FiniteSets.lean`
proves finite-set internalization into nonzero RV and algebraicity descent.
`Exchange.lean` and `FiniteFibres.lean` prove scalar exchange and the finite
infinite-fibre exceptional-set theorem over the same original real base.
Exact types, representation conventions and verification are in `STATUS.md`.

The author resolved R025–R026: 2.14 now makes its scalar scope explicit;
2.15's literal subsets were already unary, so its statement and proof remain
unchanged. See the [review record](reference/proposed-revisions/README.md) and
[resolved PDF passage](reference/section2-exchange-resolved-review.pdf).
The approved C-minimality clarification (R027) and empty-set dimension value
−∞ (R164), explicit boundary definability (R032), and the boundary proof
clarifications (R033) are applied.
Nontriviality of Γ(S) is now a standing assumption throughout the paper
(R028), as approved by the author; the former exception at the opening of
§6 is removed. Later uses are checked for any genuine need for triviality. The two approved R029 proof corrections
are applied to 2.24, whose statement is unchanged. See the
[atomic review PDF](reference/atomic-base-change-review.pdf).

`Dimension.lean` and `RVDimension.lean` implement the paper's dimension
conventions. `DiscPoints.lean` proves 2.19 and 2.21; `GeneralDiscPoints.lean`
proves the generation bridge and both cases of 2.20 in the recorded scope.
`CMinimality.lean` and `Atomic.lean` formalize the decomposition and complete
type conventions. `AtomicBaseChange.lean` uses the explicit author-accepted
input from [18] for 2.23. `AtomicDiscs.lean` and `AtomicPolydiscs.lean` prove 2.24 in all finite VF
arities, including finite tuples of RV names, using the approved R029 argument.
The combined audit covers 245 public section theorems
and 315 reused declarations; scope and remaining gaps are in [STATUS.md](STATUS.md).

See the [formalization plan](../FORMALIZATION-PLAN.md) for reuse and verification.

`DiscParameters.lean`, `DiscGeometry.lean`, `BallAlgebraicity.lean` and
`PolydiscAlgebraicity.lean` prove 2.18 for the explicit finite-radius
open/closed charts. `AtomicImages.lean` and `RVImage.lean` prove 2.26 from the
full VF graph, retaining the zero RV tag. `PrimitiveDiscs.lean` implements
the approved thin-annulus definition. `ScalarImages.lean` proves image
atomicity; 2.27–2.28 retain the explicit accepted geometric inputs from [18].
`VFImages.lean` and `RVBranches.lean` prove image atomicity and the finite
single-valued tagged branch construction before the geometric step in 2.29.
`RectangleImages.lean`, `OpenDiscGeometry.lean`, `BallConnectedSets.lean` and
`PolydiscImages.lean` prove the general ACVF image lemma.
`TaggedPolydiscImages.lean` proves 2.29 with the finite RV∞-indexed branch
family and exact row reconstruction, relative only to the accepted unary
input from [18] at the indicated real/Gamma parameter bases.
`DiscTupleParameters.lean`, `DiscTupleLogic.lean` and `DiscGroundBridge.lean`
add mixed-output parameter logic over finite-radius DC names, with global
presentation invariance and a ground-formula bridge. The completed real-base
2.25 and 2.30 scopes are recorded below; arbitrary additional DC ground
parameters remain a separate transport task. The approved R031 text correction
is applied, as are R032–R036, each with a brief resolution in its approved
review PDF. R037 is resolved by spelling out the author’s induction, and R038’s local
limit formulation is approved and applied. R039’s proof expansion and n>0 restriction are approved/applied, as is
R040/R165’s local VF-generation hypothesis and curve-selection proof.
`ScalarBoundary.lean`, `ScalarBoundaryDefinability.lean` and
`RVFiniteDimension.lean` prove the unary boundary's finiteness, definability
and dimension bound in the documented parameter scopes.
`BoundaryCoordinateExit.lean` proves the tag-preserving coordinate witness
for the higher-dimensional induction. The full result is now assembled in
`BoundaryDimension.lean` and `BoundaryCoordinates.lean`, as recorded below.
The [approved standing-base revision](reference/proposed-revisions/standing-ground-assumption-review.pdf)
is applied in the working manuscript. The previous proposal is retained as
review history; the passage formerly misnumbered §5 is in §6.


`Differentiation.lean` proves the approved tuple-value and punctured derivative
conventions, derivative uniqueness, and the partial-derivative matrix indexing.
`RVLocalConstancy.lean` proves generic constancy of actual output RV labels in
the documented real-base scope, with a separate zero-arity case.
`DiscScalarBridge.lean` identifies the scalar and unary tuple DC-name interfaces;
full 2.25 remains in progress, and the mixed-map Jacobian theorem is now
assembled in `Jacobian.lean` in its documented real-base scope.

`Boundedness.lean` implements the approved coordinatewise valuation image and
finite bounds, retaining all original Γ∞ coordinates and excluding infinity
from doubly bounded boxes. The full bounded-image Lemma 2.41 remains.

`GammaSuprema.lean` proves definable completeness and same-base definability
of suprema for actual Gamma parameters. `Limits.lean` proves the local limit
formula, local boundedness for finite affine limits, isolation and Lemma 2.43,
plus the zero-arity fact underlying the approved R039 restriction. Full 2.41 remains in progress; full 2.44 is now integrated in the real-base
scope described below.


`RVIndexedDimension.lean` records the companion dimension bound for RV-indexed
families; `RVUnionDimension.lean` proves the author's bound for this manuscript's
own dimension, including zero arity. `FiniteBranchLimits.lean` proves the local
finite-branch minimal-limit argument. `FiniteLimits.lean` proves 2.45 over the
same real ground base with arbitrary finite VF output arity; exact saturation,
smallness, graph and boundedness hypotheses remain explicit.

The R041/R042 geometric revisions and R166's eventual-affine wording are
approved and applied. Their [resolved PDF](reference/proposed-revisions/geometric-closedness-review.pdf)
shows printed pages 25–27. R043/R044's proof details are now applied as author-agreed expansions of
compressed arguments. Their statements are unchanged, and the erroneous
arity objection is explicitly withdrawn. See the [approved detail PDF](reference/proposed-revisions/annuli-partition-bounds-review.pdf),
printed pages 27–29. Root AGENTS.md requires independent paper-proof review
before assessing the referee report.

Lemma 2.54’s proof is approved and applied; its statement and bad-locus
strategy are retained. The [approved PDF](reference/proposed-revisions/fiberwise-openness-review.pdf)
shows printed pages 29–30. The [approved proof details](reference/proposed-revisions/fiberwise-continuity-details-review.pdf)
for Proposition 2.55, printed pages 30–31, are applied. The manuscript-review
pass reaches the end of §2, with R029’s additional DC-base scope still open.

`LimitGerms.lean` proves locality of minimal limits and the clopen extension
step in the approved curve-selection proof. Full Lean 2.46 still needs the
finite algebraic-choice construction and projective-chart transport. The
latest complete build/type/axiom audit is recorded in `verification/` and
`.scratch/r045-fibre-closures-verification.log` (245 section theorems, 315 reuse audits).

`UnaryLimits.lean` proves the finite-limit cardinality bound and the same-base
singleton-limit theorem for bounded unary maps. `OpenDiscPartitions.lean`
proves the direct lower bound and the minimal-limit escape contradiction for
pure VF partitions. Full 2.51 and 2.53 remain in progress; their exact scopes
and current verification are in `STATUS.md`.

`GammaFiniteFamilies.lean` proves the finite-union principle and its
infinite-fibre contrapositive for actual Gamma-indexed finite VF families,
with all nonzero RV codes retained and the same real parameter base. This
supports the proposed 2.54 proof; full 2.54 remains in progress.

`FibreClosures.lean` proves the relative fibre-closure and graph-intersection
steps for arbitrary topological spaces, with a Hausdorff graph target. Full
2.54/2.55 still need the definability, finite-choice and chart integrations
recorded in `STATUS.md`.

`AlmostContinuity.lean` integrates Lemma 2.36 as the quoted result
**[17, Lemma 8.7]**, reusing its existing checked proof and transporting the
dimension convention. This is quoted-result integration, not a new proof of
the cited theorem. Its complete audit passed 247 section theorems and 317
reuse declarations. Full 2.44 is now proved in the real-base scope; see `STATUS.md`.

`FinitaryContinuity.lean` exports the full Lemma 2.44 conclusion over the
original real base, including empty finite fibres, with the approved n>0.
The coding, branch and generic-locus modules supply its supporting proofs.
Its project/type/axiom audit passed **269 section theorems
and 323 reused declarations**; see `.scratch/lemma-2-44-verification.log`.
The section as a whole is still incomplete.

`Jacobian.lean` now integrates the full mixed-map Lemma 2.38 conclusion in
the real-base scope, with one same-base exception for existence and fibrewise
continuity and the zero-arity determinant 1. It reuses the checked derivative
and definable-Jacobian results. The latest full audit passed **272 section
theorems and 329 selected reuse declarations**, with only the three allowed
logical axioms; see `.scratch/lemma-2-38-verification.log`.

The author-accepted results of [18, §3] now have replaceable explicit
unary-disc and Gamma base-change interfaces. `NamedPolydiscAtomicity.lean`
assembles Lemma 2.25 for every finite-radius open/closed product, including
zero coordinates, without assuming the multivariable conclusion. The
containing type-generating set may be nondefinable. Closed singleton-radius
coordinates remain separate chart work. The latest full audit passed
**294 section theorems and 333 reused declarations**; see `STATUS.md`.

`PolydiscCharts.lean` and `PolydiscAtomicity.lean` now export the full
uniform open/closed Lemma 2.25 over real/Gamma ground bases. Closed radius
infinity is included in arbitrary coordinates through its actual singleton
name; chart existence is proved. The two accepted [18, §3] inputs remain
explicit. Latest full audit: **313 section theorems / 335 selected reuse
declarations**. Arbitrary additional DC ground names, Corollary 2.30 and
the remaining §2 results are separate unfinished work.

The affine case of 2.46 is now assembled in `AffineCurveSelection.lean`,
with the original-base-plus-b graph, finite nonempty values throughout
𝓜\{0}, continuity there and minimal limit {b}. The choice, algebraic model,
finite exception and clopen extension are constructed by the supporting
modules, with no extra conclusion premise. Latest full audit: **348 section
theorems / 338 selected reuse declarations**. Infinite projective coordinates
and the other recorded unfinished §2 results remain active work.

`CurveSelection.lean` now proves the full coordinatewise projective 2.46
in the recorded VF-generated real-base scope, including infinity and zero
target arity. Its full graph uses precisely the original base plus the
finite coordinates of b. Reciprocal-chart and finite-limit transport are
proved, with no additional choice or chart premise. Latest complete audit:
**371 section theorems / 342 selected reuse declarations**. See `STATUS.md`
for remaining §2 work.

`ClosedBoundedImages.lean` now exports full Lemma 2.48 over an arbitrary
real parameter base. A small temporary VF-generated base is constructed
from finite defining parameters; the original base has no VF-generation
premise. Both closedness and boundedness are proved using relative
continuity and actual finite-valued inverse-image families. Latest complete
audit: **391 section theorems / 347 selected reuse declarations**.

`ClosedBoundedHomeomorphism.lean` proves Corollary 2.49 as an actual
Homeomorph onto f(A), with its underlying map explicitly equal to f. Latest
complete audit: **396 section theorems / 347 selected reuse declarations**.
The projective topology bridge for 2.50 is active work.

`ClosedGraph.lean` and `BoundedClosedGraph.lean` now prove 2.50 in the actual
relative projective target and its bounded affine version. The two-chart
topology, graph-closure bridge, bad-input curve and projective limit
contradiction are proved. The original real base has no VF-generation
assumption. Latest full audit: **430 section theorems / 352 selected reuse
declarations**. Section 2 remains incomplete; see `STATUS.md`.

`DiscToDisc.lean` integrates the author-accepted quoted 2.31 through an
explicit [18, Proposition 3.19] input. `PartitionBoundedVF.lean` proves
both bounds in the pure VF case of 2.53, with actual finite choices and
no original-base VF-generation premise. Its mixed RV case is unfinished.
Checkpoint audit: **437 section theorems / 352 reuse declarations**; the
uniform bad-locus proof for 2.54 is now being assembled.

`FibrewiseOpenness.lean` proves both cases of 2.54 over a fixed definable
unary base, allowing empty fibres. The same-base bad locus, uniform radius
formulas, finite choices and Gamma-indexed union are constructed. Latest
full audit: **472 section theorems / 357 reuse declarations**. Work continues
on 2.55 and the other remaining §2 results.

Supporting results for 2.55 now include actual projective Hausdorffness,
fibre-graph recovery, two-chart closedness, uniform same-base fibre closure,
the product-source closed-graph criterion and both definable chart graphs.
Latest full audit: **488 section theorems / 359 reuse declarations**.
The full finite-exception conclusion of 2.55 is still being assembled.

`FibrewiseContinuity.lean` now proves full 2.55 in the real-base scope:
fibrewise continuity gives joint continuity outside a finite same-base
definable unary exception. The chart closures, closed family and exception
are constructed. Latest full audit: **499 section theorems / 360 selected
reuse declarations**. Other recorded §2 targets remain unfinished.

`FinitaryPolydiscPartition.lean` proves Corollary 2.30 over the original
small real ground base. It constructs a finite disjoint definable partition
and, on every open polydisc in each piece, the finite RV∞-indexed branch
family, full graphs over the actual disc names plus tag, point/open image
alternatives and exact reconstruction. Both compactness steps, complete
type loci and coordinate chains are proved. The unary [18, §3] results are
explicit replaceable inputs in their finite-DC parameter context.
Empty fibres, zero tags and zero source arity are included.

Latest complete audit: **541 public section theorems / 360 selected reuse
declarations**, with eight explicit accepted cited-input interfaces. The
remaining multivariate 2.35, full 2.41, 2.51, mixed 2.53 and extra DC-ground
transport obligations are still active. The current 2.30 PDF excerpt is
queued in the right panel; this does not confirm that it is visible.

RV-dimension support now includes finite-to-one maps from RV∞^m to RV^m,
restriction, dimension monotonicity, finite unions with fixed target arity,
and the strict dimension bound for sets finite over fewer existing RV
coordinates. These preserve the original real base and include zero tags.
The latest full audit passed **558 section theorems / 360 selected reuse
declarations**. Multivariate 2.35 remains in progress.

Product maps, padding by unit coordinates, input reindexing, finite-union
dimension bounds and the one-coordinate cylinder bound now compile and
are audited. The uniform-choice support promotes pointwise definable VF
points to singleton relations, takes a finite cover by compactness, and
uses finite formula priority to construct an original-base definable
choice. Its application to the actual unary boundary family remains.
Latest complete audit: **575 section theorems / 360 selected reuse
declarations**; the eight accepted cited interfaces are unchanged.

The actual unary-section boundary family now has a uniform representative
choice over S. Its pointwise premise is proved using 2.21 on partially met
RV fibres. The resulting finite-valued VF correspondence has a full
original-base graph, is RV-injective on every fibre, covers all boundary
tags, and uses singleton zero when there are none. Latest full audit:
**595 section theorems / 360 selected reuse declarations**. The partition
and zero-coordinate assembly of multivariate 2.35 remain in progress.


The full multivariate **Lemma 2.35 now passes** the project entry-point build
and exported-type/principle audit. It includes zero arity and all singleton-zero
RV factors. The original-base representative correspondence, finite zero-face
partition, retained-tag graphs, finite projection fibres, cylinder bounds,
coordinate-exit coverage and induction are proved. The actual VF-tuple export
is `lemma_2_35_vf` in `BoundaryCoordinates.lean` (namespace `DiamondIntegral.Section2`),
relative only to the three existing unary [18, §3] inputs used in 2.30.
Latest complete audit: **655 section theorems / 360 selected reuse declarations**;
the eight accepted cited interfaces are unchanged. Earlier counts above are
historical milestones. Full 2.41, 2.51, mixed 2.53 and additional DC-ground
transport remain active. No main-text change was made for this proof.


Full unary **Lemma 2.51 now passes** the entry-point build and type/principle
audit. Its singleton limit, full translated graphs, fixed-centre positive
power law, increasing radius map, inverse-neighbourhood control and equality
of entire punctured discs are proved, with no new cited input. The checked
scope is canonical ACVF with genuine saturation at an infinite cardinal,
a small real base and a compatible valuation topology. Latest audit:
**686 section theorems / 366 selected reuse declarations**. The eight accepted
cited interfaces remain unchanged; full 2.41, mixed 2.53 and general additional
DC-ground transport remain active.


Support for the author's 2.41 induction now includes original-base uniform
supremum graphs and the finite Gamma image of a unary RV map on each fixed
input value fibre. The pure Gamma bounded-image calculation uses an explicit
piecewise rational-affine background input from [18, proof of 3.18]; the
cited-interface count is now nine. Full RV-domain 2.41 is still in progress.
Latest audit: **701 section theorems / 367 selected reuse declarations**.


Full **Lemma 2.41 now passes** for both actual RV and Gamma outputs, in every
finite input arity including zero. The author's fibre-supremum induction is
implemented over the original small real base. The sole cited premise in
these exports is the recorded Gamma piecewise rational-affine background;
full 2.41 is proved. The source double bound itself excludes infinity tags.
Latest audit: **736 section theorems / 369 selected reuse declarations**,
with nine explicit cited interfaces. Mixed 2.53 and additional DC-ground
transport remain active. The main text is unchanged.


Full mixed-coordinate **Lemma 2.53 now passes** the project build and audit.
It derives the original-base RV-indexed Gamma image graph, proves each VF
fibre bound, constructs the uniform endpoint bound and applies 2.41. Empty
sources and zero VF/RV arities are included. Its explicit scope and the
remaining additional DC-ground work are recorded in `STATUS.md`. Latest
audit: **748 section theorems / 369 selected reuse declarations**, with nine
accepted cited interfaces and only the standard three logical principles.


The current numbered inventory is [COVERAGE.md](COVERAGE.md). The final
entry-point audit passes **850 section theorem declarations / 378 selected
reuse declarations**, with nine explicit accepted cited interfaces. Finite
DC-ground transport in 2.24 now includes the logical promotion/fibre proofs,
finite RV tuples and singleton ground names. Notation 2.8 and Definition 2.40
have exact companion bridges. The disc-to-disc theorem is correctly exported
as `lemma_2_32` (2.31 is the definition). The author-approved citation clarification
for R029 is applied, and R029 is fully resolved. See the
[updated PDF extract](reference/disc-ground-base-resolved-review.pdf), printed
pages 16–17. No source approval is pending.

The final DC-ground corollary is `corollary_2_30_disc_names` in
[NamedFinitaryPartition.lean](NamedFinitaryPartition.lean). It proves the
original-base finite partition and every polydisc's full finite RV-tagged
branch family. Its explicit infinite-cardinal saturation, smallness,
nontrivial Gamma and four existing unary cited inputs are retained. This
closes the last tracked §2 scope extension; no new source edit was needed.
