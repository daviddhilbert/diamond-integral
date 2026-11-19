# Section 5 — Original-language monomial decomposition and Fubini

Current adapter-resolution update, November 16, 2026: the two scoped [18]
Section 6 source adapters have been removed. `Completed18NativePositiveKernel`
uses the published generated-base kernel in
`IntegrationInACVF.Section7.CompletedSection6`, through an explicit map from
original VF objects to its closed VF presentation. The exact original positive
lift and kernel, both Fubini conclusions and the variety corollary are retained.
No universal two-order registry is assumed and no dependency source is patched.
The physical Section 7 location contains the completed unmeasured Section 6
kernel interface; no open Section 7 or measured-integration result is an input.
`prepare-dependencies.py` now checks published sources without changing them.

Current verified status, November 15, 2026: the requested scope is complete,
and both former earlier-section inputs are discharged.
`GammaQE.gamma_piecewise_rational_affine` proves the exact Gamma-linearity
interface from QE. `completed18GroundLiftInput C hc` constructs the exact
positive lift, its object formula, surjectivity and special kernel over the
original ground from completed [18] proofs. The actual positive RV and VF
presentation dictionaries and the definable-closure parameter transport are
proved. The unfinished [18] Section 7 supplies no input.

`Section5DischargedInputs.lean` gives the bounded/geometric Fubini entry points
and all intrinsic field lifting inputs. `VarietyCorollaryDischarged.lean`
instantiates the final actual-variety corollary. Full audit 75 (publication package) passes with
1357 public definitions/structures and 2234 theorems, using only `propext`,
`Classical.choice` and `Quot.sound`. Both `accepted_inputs` and remaining-work
lists are empty. Exact [18] overlay and scope-adapter hashes are checked by
`verify.py`; see the outer `Section5/reference` records.

To reproduce the checked build from a fresh clone, use the pinned Lean 4.35.0
toolchain and fetch the pinned Lake packages, then run:

```sh
lake update
python3 'section 5/prepare-dependencies.py'
lake build DiamondIntegral
lake env python3 'section 5/verify.py'
```

The preparation script restores the 252 additional [18] sources from
`dependency-overlay/` and the 39 compatibility corrections already recorded
in Sections 2 and 3. It checks revisions and hashes and preserves unexpected
local edits. `--check` validates an already prepared checkout without writing.
A fresh-clone reproduction and the preservation check are recorded in
`verification/dependency-preparation.log`. CI uses the same preparation and
also runs the Section 5 type/principle audit. The proof bodies are unchanged
from the completed Section 5 audit.

The following development notes record earlier intermediate states. Their
unfinished-input descriptions are superseded by the current status above.

Author scope: omit the cross-section expansion and the computational
results cited from [19]. Prove Lemma 5.12 and everything after it;
needed HK arguments must be proved locally. No HK theorem is an input.

Formalization has started. `ValueInducedRectangles.lean` proves finite
consolidation of rectangle covers into pieces cut out by values alone,
including overlapping Gamma supports and fixed active-value slices.
`ValueInducedCharts.lean` transports this partition through a value-compatible
coordinate equivalence and proves the product identity for each source piece.
`GroundValueCells.lean` and `GroundRectangleAssembly.lean` now connect
this assembly to actual original-ground RV/Gamma definability. The entry
point is `Section.lean`.

The mixed normal-form theorem constructs a finite definable partition of
the actual joint value image, fixed-value residue factors and Gamma factors
over the original real/Gamma base. It proves the active values individually
definable at that base, and supplies the rectangle cover using the locally
proved Section 3 separation result with its actual model/base hypotheses.
`AngularValuePartition.lean` now transports this mixed result through one
angular cell's actual integral monomial coordinates. The resulting source
pieces are cut out by a disjoint partition of the original value image;
all sets and product bijections are over the original real/Gamma base.
Its coordinate-image identity records the monomial chart itself.
`GlobalAngularPartition.lean` supplies the original-value-induced initial
angular partition. `MonomialDecomposition.lean` assembles the local charts,
discards empty pieces and proves nonemptiness and exact singleton residue
values. `MonomialMatrixForm.lean` constructs the GL_n(Z) matrices with their
two-sided integral inverses, proves their standard block-order interpretation,
and exports `DiamondIntegral.Section5.monomial_decomposition_5_12`.

Lemma 5.12 is complete for its stated nonzero-RV input, in the recorded
canonical ACVF00 model with actual saturation, both smallness assumptions
and nontrivial definable Gamma. The statement map is
`verification/paper-target-5-12.json`. It includes the original value
partition, all original-base definability and actual monomial image
identities. The empty input and arity zero are allowed. Later Kummer and
Fubini results remain incomplete; zero-coordinate/RV[k]-label adapters
belong to those later results, rather than enlarging 5.12's stated scope.

Run `python3 'section 5/verify.py'` with Lean/Lake 4.35.0 on PATH.
Verification builds the entry point, prints all public definition and theorem
types, checks principle dependencies, scans for proof placeholders, and
records exact source hashes under `verification/`. The new ground modules
import the actual local Section 3 ACVF definability and separation APIs.
The manifest pins, actual dependency revisions and hashes of the existing
copied source patches are recorded; no dependency source is edited here.

The algebraic part of Remark 5.13 now compiles. `LaurentKummerBasis.lean`
constructs the actual finite expansion, power basis, degree, generation and
irreducibility. `FiniteKummer.lean` and `LaurentKummerActions.lean` prove the
full finite classification, coefficient action and valuation preservation.
`PuiseuxField.lean` constructs the actual Puiseux union of finite Laurent
levels in rational Hahn series. `CompatibleRootSystems.lean` and
`HahnCharacterActions.lean` construct the global character action;
`PuiseuxCharacterActions.lean` restricts it to the actual field over its full
Laurent base and proves faithfulness. `PuiseuxGalois.lean` proves the converse,
bundles the Galois-group equivalence and proves all base automorphisms
valuation-preserving. The complete type and principle audit passes.
The exact statement mapping is `verification/paper-target-5-13.json`.
`PuiseuxRV.lean` proves the actual principal-unit quotient normal form;
`PuiseuxRVActions.lean` proves its faithful action, full lifting and bundled
Galois equivalence. `PuiseuxRVBase.lean` identifies the fixing subgroup with
the RV image of the entire Laurent base.
`PuiseuxRVLanguage.lean` constructs the concrete full original LRV structure
and its canonical totalization. `PuiseuxInducedRV.lean` proves the full
induced-RV automorphism identification, including every original formula
with VF quantifiers and parameters from the full Laurent base.
`PuiseuxCanonicalPresentation.lean` instantiates the earlier presentation:
the tagged VF ring equivalence and its Hahn-valuation compatibility are
proved. Its ACVF-model hypothesis is explicit; canonical totalization does
not by itself prove Newton–Puiseux algebraic closedness or construct the
saturated ambient extension.

The finite-level comparison now has checked support for all finite
Kummer multipliers, auxiliary framing with zero coordinates, the
existential-root construction for sets and graphs, and actual
constructible complex coordinates for original-base RV sets. The reverse
construction now has proved original-base definability via an actual definable
Kummer-root source and RV monomial map. Both finite-stage set constructions
are proved inverse, including zero coordinates. Root changes, level inflation
and products are checked; every finite complex cyclic representation has
a proved character basis.
`RESFiniteWitness.lean` connects the finite stabilized positive-relation
criterion to the actual ungraded RES quotient, including its degree and
value-fiber relations. The coefficient assembly for Gamma integration is checked using actual
fibre integrals. The full Theta ring comparison, the geometric presentation
bridge, relative RV/Gamma push and the full Fubini theorem are
still unfinished. Support declarations are not recorded as completed
numbered theorems.


The native object and ring bridge is now explicit. `EmptyGammaGround.lean`
proves the exact conversion to original real-parameter definability.
`CanonicalRESObjects.lean` gives every literal finite-value RV domain an
actual finite-label RES object, retaining zeros and the base.
`NativeRESClasses.lean` and `RESSetOperations.lean` prove independence from
those labels and the actual native products and scissors.

`RationalDiagonalActions.lean` and `RationalFrameComparison.lean` express
framing and descent independently of common denominators.
`RationalBijectionDescent.lean` descends arbitrary invariant constructible
bijection graphs to original-base bijections. `DiagonalRESRingMap.lean`
constructs `diagonalToRES`, an actual ring homomorphism from the explicit raw
diagonal constructible presentation to the native ungraded RES ring, with
all defining relations checked. `RationalFramedMaps.lean` proves the forward
full-graph transport. `DiagonalFinitePartitions.lean` checks finite invariant
constructible additivity. The forward map is now constructed through the
actual native positive presentation, graded direct sum and ring completion,
and is proved to descend through the actual forget-degree ideal.
`RESRawComparisonEquivalence.lean` proves `rawRESComparison`, including both
composition identities on all finite value supports. This completes the raw
native/diagonal-constructible ring comparison.
`RESFibreComparison.lean` computes the actual native fibre generators;
`RESCharacterQuotient.lean` proves their exact correspondence with character
line differences. `DiagonalAffineSpaces.lean` identifies that ideal with
all actual diagonal linear-action relations, including arbitrary equivariant
factors. `RESLinearActionQuotient.lean` constructs the resulting reduced
native/modified-constructible ring equivalence. The remaining comparison
obligation is the geometric variety bridge. Its affine ingredients now
compile: `EquivariantAlgebraGenerators.lean` gives finite character
algebra-generators, `EquivariantAffineEmbedding.lean` constructs an actual
closed Spec immersion and proves its equivariant algebra square, and
`InvariantAffineStratification.lean` gives finite disjoint invariant closed
pieces inside displayed affine opens of a good quasi-compact separated
scheme. The closed-subscheme and variety-ring assembly and the
characteristic-zero piecewise algebraic-isomorphism theorem for constructible
bijections remain. Relative RV/Gamma push and full Fubini remain unfinished.

Manuscript approvals and the approved final-corollary PDF are recorded in the
surrounding Section5 review directory. The canonical Section 5 manuscript
changes through R095 and the final corollary are incorporated into this
isolated checkout. Section 5 manuscript review is complete; formalization
continues.
No commits or pushes are authorized.


The finite rational graph and invariant-stratification stage passes the full
audit (`Section5/.scratch/finite-comparison-audit-15.log`, 296 selected public
definitions/structures and 462 theorems; only standard logical principles).
Global graph uniqueness transfers to every elementary model of the complex
field. Compactness then supplies finite rational descriptions with original
complex coefficients, for all finite output tuples, with a common nonzero
denominator on each piece. `PrincipalRationalMaps.lean` constructs the actual
Spec morphisms from principal affine opens and checks their complex points.
`InvariantConstructibleStrata.lean` constructs finite invariant locally closed
strata adapted to any finite constructible family, with clopen restrictions
of that family. The actual scheme-piece isomorphism and usual variety-ring
assembly, and full Fubini, remain to be completed.


The actual affine-scheme adapter stage passes the full audit
(`Section5/.scratch/finite-comparison-audit-16b.log`, 326 selected public
definitions/structures and 517 theorems; standard logical principles only).
Complex points detect equality in reduced finite-type coordinate algebras,
invertibility in finite-type complex algebras, and equality of constructible
scheme subsets. Invariant closed affine subsets now have actual reduced
closed subschemes, descended coordinate actions, scheme actions, and
equivariant inclusions. Basic constructible schemes have exact immersion
images and a proved two-way complex-point correspondence. The factorization
`complexPointBasicFactor` is constructed from the point condition.
`BasicRationalPointIso.schemeIso` constructs an actual reduced affine-scheme
isomorphism from mutually rational point descriptions. The finite
equivariant cover/partition, usual variety-ring assembly, relative RV/Gamma
push and full Fubini are still pending; no additional numbered result is
marked complete.


The finite geometric graph-piece stage passes the full audit
(`Section5/.scratch/finite-comparison-audit-17.log`, 340 selected public
definitions/structures and 550 theorems; standard logical principles only).
`complex_constructible_bijection_algebraic_pieces` now constructs a finite
disjoint partition of every actual pure-field definable complex bijection
graph by reduced affine basic graph schemes, with both coordinate
projections actual immersions. The intermediate basic partition covers all
scheme points and retains fixed original-coefficient rational forward and
inverse expressions. `locallyClosedAffineScheme` also constructs the actual
reduced scheme of every locally closed affine-spectrum subset, with an
immersion and exact scheme-point image. Equivariant source/target strata
and regular-map gluing, the usual geometric equivariant variety-ring
assembly, and full Fubini remain unfinished.


The reduced-scheme gluing stage passes the full audit
(`Section5/.scratch/finite-comparison-audit-18.log`, 374 selected public
definitions/structures and 627 theorems; standard logical principles only).
Reduced immersions have unique lifts from actual image containment. Actual
group actions restrict to invariant locally closed strata. Finite invariant
input strata carry regular maps obtained by gluing affine graph branches;
complex-point single-valuedness proves the overlap equalities. Transformed
graph compatibility proves equivariance of the glued maps. Forward/inverse
branch certificates give common reduced fibre-product pieces whose two
projections are actual immersions. Arbitrary reduced induced subschemes and
reduced fibre products, their universal maps, point ranges and induced
group actions are constructed. Finite common-piece coverage, the usual
equivariant variety-ring assembly, and full Fubini remain unfinished.


The instantiated equivariant decomposition stage passes the full audit
(`Section5/.scratch/finite-comparison-audit-19.log`, 397 selected public
definitions/structures and 666 theorems; standard logical principles only).
`complex_equivariant_bijection_decomposition` now constructs certified
invariant regular source and target strata from an actual pure-field
definable finite diagonal-equivariant complex bijection. The common reduced
pieces have actual equivariant immersion projections and unique coverage
on both sides at every scheme point. Prime avoidance proves the goodness
of every finite action on a reduced scheme immersed in an affine scheme.
`EquivariantVarietyRing` defines the actual geometric target using reduced
separated finite-type complex schemes, finite compatible-root actions,
equivariant scheme isomorphisms, closed/open scissors and reduced fibre
products. `affineObject` and `immersedAffineObject` construct genuine target
objects. The two geometric comparison ring maps and their scissor/product
proofs, and full Fubini, remain unfinished. No additional numbered theorem
is marked complete.


The literal finite-witness stage passes the full audit
(`Section5/.scratch/finite-comparison-audit-20.log`, 443 selected public
definitions/structures and 701 theorems; standard logical principles only).
`res_equality_iff_literal_family_witness` gives an equivalent finite native
RES criterion with actual coefficient-object families, actual underlying
bijection graphs or definable value-fibre pairs, orientations, one common
stabilizer and finitely many actual total-family RES isomorphisms. No
positive-class equality is accepted as witness data.
`LiteralFamilyWitness.taggedBijection` constructs one literal RV zero/one
tagged same-base bijection between actual RES objects; all finite value
supports and finite label maps are proved. The expanded certificate retains
the degree-forgetting isomorphism pairs; consolidating those into the
common stabilizer gives the manuscript's fibre-only display and remains
to be packaged. First-order validity/uniformization and preparation of the
whole witness, relative RV/Gamma push and full Fubini remain unfinished.
`GraphDecompositionVarieties` also turns every source/target stratum and
common piece into a genuine geometric variety object, and proves that
both common-piece maps are equivariant morphisms over the complex base.
The geometric comparison ring maps and scissor/product assembly remain.

November 14 continuation, audit 22: the whole finite-family preparation
adapter and fixed finite-fibre validity formulas are checked. Geometric
closed/open scissors now imply arbitrary finite immersed partition sums;
actual reduced common refinements prove independence of constructible
classes. Intrinsic rational diagonal affine actions, their finite-level
compatibility, and geometric value invariance under actual equivariant
constructible bijections are checked, as are the empty and unit values.
Multiplicativity, the inverse geometric comparison, and full Fubini remain
in progress. No additional numbered result is marked complete.

November 14 continuation, audit 24: the actual forward geometric ring
map is checked, including multiplication via genuine reduced equivariant
products. It is surjective: every good finite-action variety has an
actual finite invariant affine presentation, and each affine piece has
a checked equivariant closed embedding into rational diagonal affine
space. Coordinate algebras, their finite type and their actions are
constructed from the scheme data. Injectivity and inverse comparison,
the final quotient comparison and full Fubini remain unfinished.
The native RES composite retains its explicit Puiseux ACVF-model
hypothesis. No further numbered statement is marked complete.


Raw geometric comparison, November 14: `DiagonalConstructible.rawGeometricComparison` now proves an unconditional ring equivalence with the actual good finite-action variety presentation. Both maps, presentation independence, actual closed/open scissors, products and both inverse identities are checked. The native composite `PuiseuxOriginal.rawVarietyComparison` retains the explicit concrete Puiseux ACVF hypothesis. Full audit 25 passed with 545 definitions and 908 theorems, using only the recorded logical principles. The geometric all-linear-action quotient and full Fubini remain.


Geometric quotient comparison, November 14: full audit 26 passed (561 definitions, 927 theorems). `finite_linear_affine_diagonalization` constructs actual equivariant scheme isomorphisms for every finite linear representation; `geometric_linearActionIdeal_correspondence` proves exact ideal correspondence, including arbitrary multiplicative factors. `DiagonalConstructible.geometricLinearActionComparison` is unconditional. The native composite `PuiseuxOriginal.theta_5_14` retains the explicit ACVF-model hypothesis on the concrete Puiseux field. Relative RV/Gamma push, full finite-witness descent, Theorem 5.17 and the final corollary remain.


Native bounded retraction and finite certificate support: full audit 27 passed (581 definitions, 947 theorems). `nativeRVEvaluation` instantiates the checked T001 transport and takes values in the actual dimension-free reduced RES ring; its RES/Gamma evaluations and arbitrary-label invariance are proved. Fixed finite quotient-value bounds, the five cylindrical fibre-shape validity formulas and their quotient semantics, reconstruction of actual Gamma cells, and full-quotient-domain validity are checked. Recursive Euler-package assembly, full native witness descent, relative RV/Gamma push and the Fubini targets remain.


Recursive Euler syntax and actual monomial evaluation: full audit 28 passed (594 definitions, 960 theorems). A valid `EulerFormulaCertificate` computes the actual native Gamma integral; every cell is decoded as an actual cylindrical cell, with quotient invariance and full global disjoint coverage certified. Existence and original-base promotion of the certificates into the entire native witness family still need assembly. The native monomial and relative chart formulas preserve arbitrary labels and every torus power; full relative Gamma push and Fubini are not yet proved.


Original-base Euler certificate existence: audit 29 passed (603 definitions, 981 theorems). `original_euler_certificate_exists` promotes the source and every cell predicate over the original base and supplies a valid finite first-order certificate for both actual Gamma Euler integers. Parameter-free original Gamma relation formulas are constructed; cell trees are actual finite native predicate schemata. Whole formula-tree validity and shape are invariant under exact predicate-row agreement. Certificate preparation and its integration into full native RES witness uniformization remain, together with relative RV/Gamma push and the final Fubini targets.


Whole Euler package preparation: audit 30 passed (608 definitions, 996 theorems). `prepare_original_euler_certificate` constructs one genuine original-base special bijection preparing the source and every primitive cell predicate. Whole validity descends to the RV key; the certificate retains both computed integers. `FiniteValueDomainValidity` supplies first-order value bounds using equivalence formulas only on the actual source. Native RES support and full witness-family uniformization, relative RV/Gamma push, and the final VF Fubini statements remain.


Native RES schema validity: audit 31 passed (619 definitions, 1013 theorems). Fixed first-order bounds cover full native RV value patterns, including zeros. Valid RESSetSchema rows realize actual native RES objects with finite clean labels; every actual RES chart promotes to one over the original base. RESSetSchema.valid_definable proves original-Gamma definability of its genuine validity locus via projected tuples of distinct values. Full bijection/relation witness packages, their uniformization, relative RV/Gamma push and the final Fubini statements remain.


Native RES graph certificates: audit 32 passed (627 definitions, 1031 theorems). Valid graph schemata realize actual native underlying chart isomorphisms and native RES equality. Every actual RES bijection over a displayed parameter promotes to such an original-base schema, with the whole graph retained. Saturation gives uniform finite support bounds; one genuine special bijection prepares arbitrary finite domain/graph families and preserves complete bijection validity. Whole Euler validity loci and full literal relation-witness uniformization remain, followed by relative RV/Gamma push and the final Fubini targets.


Whole Euler catalog uniformization: audit 33b passed (631 definitions, 1057 theorems). Actual original-base validity is proved for nonzero quotient domains, cylindrical fibres and steps, full finite partitions, recursive trees and entire Euler certificates. Every fixed quotient source has an actual original-base certificate; saturation selects a finite catalog. One genuine special bijection prepares all primitive predicates of that catalog simultaneously. Varying Gamma-value/RES relation witnesses, their complete finite-family assembly, full relative RV/Gamma push and the final Fubini targets remain.


Native primitive relation schemata: audit 34 passed (655 definitions, 1084 theorems). Varying Gamma values are encoded by full nonempty singleton-value RV fibres, promoted over the original base, and remain the same actual Gamma value after preparation. Their actual native torsor classes equal the residue torus. Underlying-bijection and fibre primitive schemata, actual native realization, finite catalog preparation, coefficient-object lists, orientations and native product-domain/support-bound constructions are checked. Complete total stabilization graphs, relative push and the final Fubini targets remain.


Literal native RES arithmetic: audit 35 passed (677 definitions, 1111 theorems). Tagged coproducts retain exact source rows, tags and zero padding with explicit finite support bounds. Their class formula follows from actual original-base cuts and coordinate bijections. Product classes, arbitrary-degree canonical row presentations, complete coefficient predicate lists and term preparation are checked. Finite expression schemata now realize empty domains, sums and products as their actual native RES classes. Complete stabilized witness assembly, relative push and the final Fubini targets remain.


Complete stabilized schema soundness: audit 36 passed (702 definitions, 1143 theorems). RESStabilizationSchema retains all coefficient objects, orientations, one common stabilizer and a literal total-domain bijection graph. Its full validity is original-base definable and implies actual native RES equality by cancellation. Finite expression recoding, actual expression-bijection soundness, and one-step preparation of arbitrary finite mixed VF/RV parameter families are checked. Existence/uniformization of every complete stabilization schema, relative push and the final Fubini statements remain.


Original layout certificates: audit 37 passed (723 definitions, 1163 theorems). Complete native relation trees include actual underlying graphs, full value-fibre pairs, arbitrary finite coefficients and reversal. Literal expression layouts carry purely formal polynomial identities; original-base validity of a complete layout and its full total bijection implies actual native equality. These formal identities and the whole validity package survive row recoding. Actual native tags and arbitrary-degree underlying chart maps are checked. Existence from every old literal family witness, compactness/preparation assembly, relative push and the final Fubini targets remain.


Whole catalog preparation: audit 38 passed (730 definitions, 1167 theorems). One genuine original-base special bijection prepares every primitive domain and graph of a finite complete layout catalog with mixed VF/RV parameters, retains the original RV coordinates, and preserves entire witness validity. Exact raw-domain agreement and actual native sum/product bijections are checked. Promotion of the old finite stabilized family witness, its finite uniformization, relative push and the final Fubini targets remain.


Complete native equality descent: audit 39b passed (753 definitions, 1193 theorems). Every old literal family witness promotes to a whole original-base layout certificate, preserving all coefficient occurrences, orientation choices, degree-filtered tagged domains and the actual total bijection. Native RES equality is equivalent to existence of a valid certificate; saturation selects a finite catalog. The theorem native_res_equality_descends proves actual equality over the prepared RV base using one genuine special bijection. One joint preparation also preserves complete RES and Euler catalogs with mixed RV parameters. Residue/Gamma family templates retain the empty-fibre region. Full relative push, the final VF Fubini statements and concrete Puiseux ACVF-model existence remain unfinished.


Scalar Gamma parameter control: audit 40 passed (766 definitions, 1213 theorems). Lemma 5.12 now yields a finite original-ground partition for every actual scalar Gamma function on a nonzero RV domain, on which its graph depends only on the input values. A finite collection has one common partition. No definable-closure span identity or angular section is assumed. Native bounded evaluation on actual objects respects products, finite disjoint partitions and underlying bijections of arbitrary degrees. The varying-torsor identity, full relative Gamma push and the final VF Fubini statements remain.


Native scalar torsor Fubini: audit 41b passed (778 definitions, 1247 theorems). The theorem native_scalar_torsor_fubini proves the full varying scalar value-torsor identity over an arbitrary original-ground nonzero RV domain, for both Euler kinds. Every monomial coordinate map and packed torsor/product bijection is actual and definable over the original base; the reconstructed Gamma singleton graph has the actual Euler integral of its base. Complete finite source and graph partitions give the global identity with one torus factor. Several torsor coordinates, zero-coordinate RV bases, full relative Gamma push, the final VF Fubini statements and concrete Puiseux ACVF-model existence remain unfinished.


Actual Gamma fibre values, November 14: full audit 42 passed (789 definitions, 1272 theorems). The varying tuple-torsor formula now has exact coordinates and the factor g^r for every r. Actual mixed RV/Gamma families have finite-range Gamma fibre Euler values and original-ground definable level sets. Cylindrical graph, band, ray and line fibres have their actual Gamma Euler factors over arbitrary definable bases, with either coordinate order. Full relative RV/Gamma push, the final VF Fubini statements and concrete Puiseux ACVF-model existence remain unfinished.


Native cylindrical fibre formula, November 14: audit 43b passed (803 definitions, 1298 theorems). The actual family theorem native_described_cylinder_fubini proves E(Y) = chi(shape) g E(X) for graphs, open bands, either ray and lines over arbitrary original-ground nonzero RV bases, for both Euler kinds. Unique endpoints are recovered as actual original-ground maps from complete definable fibre predicates. Adapted monomial charts, finite source partitions and all RV output representatives are retained. Full relative Gamma push, final VF Fubini and concrete Puiseux ACVF-model existence remain.


General relative Gamma calculation, November 14: full audit 44 passed (816 definitions, 1322 theorems). native_relative_gamma_fubini_partition applies to every actual original-ground mixed nonzero-RV/Gamma family. It constructs a finite disjoint original-ground base partition with constant actual Gamma fibre Euler integers and proves E(Y) = g^n sum_i c_i E(A_i), for both Euler kinds. Complete original Euler trees realize actual relative cylindrical cell families, and whole certificates partition the actual total family. The conversion to the canonical Euler-level sum, raw RV bases containing zeros, VF-to-RV monomial preparation and full Theorem 5.17/corollary remain. The concrete Puiseux ACVF-model hypothesis also remains explicit.


Relative Gamma push over all RV bases, November 14: full audit 45 passed (829 definitions, 1342 theorems). native_relative_gamma_fubini and native_raw_relative_gamma_fubini give the canonical actual Euler-level sum E(Y) = g^n sum_e e E(X_e), for both Euler kinds. Raw RV bases may contain zeros. rawGammaRepresentativeBijection is an actual original-ground bijection from the full original-base family of RV representatives to the coded lift, and rawRVGammaFibreEulerValue_code identifies its actual integral over the exact raw parameter base. Finite integer weighted native integrals are proved independent of auxiliary finite partitions. Whole VF-to-RV monomial-family preparation, total finite RES witness evaluation, full Theorem 5.17/corollary and the concrete Puiseux ACVF-model hypothesis remain.


Whole rectangle package preparation, November 14: audit 46 passed (845 definitions, 1360 theorems). Arbitrary raw RV domains have finite actual original-ground product decompositions and their native class formula. Complete rectangle schemata retain source domains, RES factors, full Gamma supports, whole Euler certificates, disjoint coverage and actual graph validity. Their genuine validity loci and recoding are proved. prepare_rv_rectangle_catalog uses one genuine special bijection to prepare every primitive of a finite catalog over mixed VF/RV parameters. Promotion/existence of every whole rectangle package, total finite RES witness evaluation and full VF Fubini remain, as does concrete Puiseux ACVF-model existence.


Whole RV rectangle descent, November 14: audit 47 passed (850 definitions, 1374 theorems). Every actual rectangle promotes to a complete original-base schema with its exact source, actual product bijection and whole Euler certificate. Every fixed RV row has a valid finite package; saturation selects a finite catalog. rv_rectangle_families_descend proves that one genuine original-base special bijection transports this complete catalog from mixed VF/RV parameters to its RV key, including zeros and empty rows. This discharges the monomial-family package existence and descent step. Evaluation of total RES witness families, the final VF assembly for Theorem 5.17/corollary and concrete Puiseux ACVF-model existence remain.


The full audit 48 passes (`Section5/.scratch/finite-comparison-audit-48.log`):
868 public definitions/structures and 1408 theorems, with only the standard
logical principles. The literal total-family Gamma and rectangle calculations
are now proved. `originalRVTotalBijection` realizes a complete original-base
family graph as an actual total RV bijection. `original_gamma_total_value`
and `original_product_total_value` apply relative Gamma Fubini while keeping
all raw RV parameters and representatives, including zeros.
`RVRectangleDecompositionSchema.total_native_value` evaluates every prepared
finite product package as the sum of its full residue-family contributions.
The remaining Fubini work is total stabilized RES-family algebra and the
uniform VF comparison, followed by Theorem 5.17 and the corollary. The native
comparison still has its explicit concrete Puiseux ACVF-model hypothesis.
`AdditivePresentationMultiplication` supplies an abstract positive relative
ring construction and an additive forgetful map; its actual relative-family
instantiation is still being proved. No new numbered result is marked complete.


The full audit 49 passes (`Section5/.scratch/finite-comparison-audit-49.log`):
881 public definitions/structures and 1421 theorems, using only standard
logical principles. The geometric retraction and exact common-degree
localization criterion are now checked through the actual lifting quotient.
OriginalRVPointwiseValues proves that original-base saturation selects a
finite catalog of actual fibre-bijection graphs and that their literal
total native values agree. The complete Fubini assembly is still pending.
The author-requested geometric variant is documented in the two-page
investigation PDF; the approved manuscript has not been changed.


The full audit 50 passes (`Section5/.scratch/finite-comparison-audit-50.log`):
904 public definitions/structures and 1453 theorems, with only the standard
logical principles. The actual relative RV-family semiring and its ring
completion are now instantiated. Formal RES expressions evaluate in this
relative ring, while `nativeRelativeRVForget` takes only additive total
values. The full original-base stabilization witnesses preserve these
values, including arbitrary shared-base coefficient families and varying
value torsors. `native_res_family_fubini` proves that pointwise equality
in the actual native RES quotient over an arbitrary raw RV base gives
equality of literal total native values, for both Euler kinds. Its proof
uses a finite original-base catalog of whole witnesses and an actual
base partition. The remaining Fubini work is the positive RES realization
of signed rectangle contributions and the global VF comparison. Full
Theorem 5.17 and its corollary are still pending; the explicit concrete
Puiseux ACVF-model hypothesis in the comparison also remains.


Full audit 51 passes (`Section5/.scratch/finite-comparison-audit-51.log`):
912 public definitions/structures and 1481 theorems, using only the standard
logical principles. `native_rv_family_fubini` now proves Fubini for arbitrary
original-base raw RV families: equality of actual native row values over
every exact parameter base implies equality of literal total native values
over the original ground. Zero coordinates and empty rows are included.
Finite original-base rectangle catalogs provide actual positive RES
expression families for every signed contribution, with checked fibre
and total evaluation formulas. The RV-family theorem uses the proved
native RES-family Fubini result. Full Theorem 5.17 remains pending at the
VF level: uniform original fibre lifts, joint preparation of both rectangle
packages and their full RES witnesses, and the global lifting comparison.
The concrete Puiseux ACVF-model hypothesis in 5.14 is also still explicit.
The author is reviewing the geometric note before deciding on that variant;
no further geometric VF-Fubini formalization has been undertaken.


Full audit 52 passes (`Section5/.scratch/finite-comparison-audit-52.log`):
933 public definitions/structures and 1520 theorems, using only the standard
logical principles. `native_rv_equality_descends` now constructs complete
original-language witnesses for actual native RV fibre equalities and
transports them to the prepared RV parameter base through one genuine
special bijection. Both rectangle decompositions, every Euler certificate,
the signed positive-expression identities and the full stabilization
bijection graph are retained. Witness existence and finite saturation
catalogs are proved; no change-of-base injectivity is assumed. The
remaining VF assembly requires uniform original fibre representatives,
finite nonzero labels and actual lift bijections, inclusion of their base
and label formulas in the joint preparation, and the global finite-label
lifting comparison. Full Theorem 5.17 and its corollary are still pending.
The concrete Puiseux ACVF-model hypothesis in the comparison also remains.


Full audit 53 passes (`Section5/.scratch/finite-comparison-audit-53.log`):
946 public definitions/structures and 1543 theorems, with only standard logical
principles. Every actual native RV fibre representative now promotes to
an original-base finite schema retaining its literal domain, complete
nonzero label graph and a uniform finite reverse-fibre bound. Genuine
first-order validity and exact recoding are proved. The joint preparation
also accommodates arbitrary finite extra base predicates and label graphs.
The finite-label argument for the global RV object is proved using its
actual VF lift, including reconstruction from a bijection with a native
finite-RV-fibre VF object. Uniformization of the actual fibre VF lift
bijection graphs and the final global VF assembly still remain, as does
the concrete Puiseux ACVF-model hypothesis. No numbered Fubini conclusion
is marked complete. The geometric note awaits the author's decision.


Full audit 54 passes (`Section5/.scratch/finite-comparison-audit-54.log`):
960 public definitions/structures and 1563 theorems, with only standard
logical principles. Actual mixed VF/RV domains and complete native
bijection graphs now have checked sorted original-language presentations
in both directions. `native_vf_lift_equality_schema_at_parameter` combines
both actual VF lift bijections, finite nonzero RV representatives and the
whole stabilized native RES equality. Its validity is genuinely first
order; saturation selects a finite original-base catalog of whole
packages. The global prepared-base and VF lifting assembly, the full
Theorem 5.17/corollary and the concrete Puiseux ACVF model remain unfinished.
The geometric variant remains a polished review note, awaiting the author's
decision before any further variant-specific formalization.


Full audit 55 passes (`Section5/.scratch/finite-comparison-audit-55.log`):
971 public definitions/structures and 1579 theorems, using only standard
logical principles. Joint preparation of each whole VF witness now
transports both finite nonzero RV label schemata and the full stabilized
RES equality. `nativePreparedParameterBase` constructs the actual prepared
RV parameter base over the original ground, retaining every old RV
coordinate. `nativePreparedVFLift_row_values` proves genuine finite-label
validity and actual native equality at every point of this base. Actual
mixed total families and complete total VF bijections are also checked.
The final identification of these families with the global RV lift,
VF integration and the full Theorem 5.17/corollary remain; the concrete
Puiseux ACVF model also remains explicit.


Full audit 56 passes (`Section5/.scratch/finite-comparison-audit-56.log`):
977 public definitions/structures and 1592 theorems, using only standard
logical principles. The actual total RV map `(s,t,u) ↦ (s,p_(s,t)(u))`
now has a complete original-ground graph and nonzero-label proof. Its
literal VF lift domain is checked. The prepared total native equality is
exported as `nativePreparedVFLift_total_values`. The actual inherited
Gamma point/special-map presentations and mixed product bijections now
have native full-graph bridges with exact value formulas. Every VF
realization of an actual prepared key lies in the prepared base by the
proved RV-pullback identity. The final global VF identification, its
zero-coordinate strata and integral/corollary assembly remain, together
with the concrete Puiseux ACVF-model hypothesis.


Full audit 57 passes (`Section5/.scratch/finite-comparison-audit-57.log`):
1005 public definitions/structures and 1640 theorems, using only standard
logical principles. Actual mixed map fibres now have literal original
formulas over the exact parameter base, and their total is actually
bijective to the original source. The genuine positive lifting hypothesis
for two actual native maps yields a finite partition of their actual
base, with one complete witness on each nonempty piece. Preparing the VF
base is now an actual native bijection of total mixed families, preserving
all old RV parameters and finite RV fibres. Fixed zero strata, removal of
fixed zero VF coordinates, key attachment, source preimage partitions and
finite native VF scissors/additivity are checked. The final identification
of the prepared images as RV lifts, the actual VF integral/corollary
assembly and the concrete Puiseux ACVF model remain unfinished.

Author approval, November 14, 2026: the geometric version of Theorem 5.17 is incorporated after the final corollary and added to the formalization scope. The approved statement uses the ungraded affine-localized intrinsic RES target. The proof selects finite denominator-clearing witnesses before preparation, pads with residue affine lines, applies geometric relative RV Fubini, and normalizes in the common total degree. NativeGeometricRetraction and GeometricDegreeClearing already prove the actual normalization and finite common-degree equality criterion; the full VF theorem remains unfinished. The adopted manuscript fragment compiled and both rendered pages were inspected.

Full audit 58 passed (Section5/.scratch/finite-comparison-audit-58.log): 1042 public definitions/structures and 1695 theorems. It includes the actual geometric normalization and positive RV affine padding, the prepared VF pullback and full RV key coordinate maps, the actual zero-stratum raw-value sum, and the native VF integral with bounded/geometric lift formulas. Only the standard Lean principles occur. The full bounded/geometric VF Fubini, final corollary and concrete Puiseux ACVF-model obligation remain unfinished.

Full audit 59 passed (Section5/.scratch/finite-comparison-audit-59.log): 1057 public definitions/structures and 1726 theorems. NativeVFFubini.nativeBoundedVFFubini proves bounded Theorem 5.17 for actual original-Gamma maps, in the recorded GammaGroundContext with the precise accepted Section 3 YinGammaGroundUnmeasuredLiftInput. NativeVFFubiniVanishing proves intrinsic positive fibrewise vanishing and its preservation by any ground comparison. NativeRVRealExtensions, OriginalConstantRVDomains, GeometricPaddedRVRows and NativeGeometricLiftValues check the actual geometric denominator padding over every fibre base and its VF lift-value formula. Full geometric VF Fubini, finite affine-chart/global Theta corollary specialization and the concrete Puiseux ACVF-model proof remain unfinished. No HK result is assumed.

Full audit 60 passed (Section5/.scratch/finite-comparison-audit-60.log): 1069 public definitions/structures and 1770 theorems; only standard Lean principles. NativeGeometricVFFubini.nativeGeometricVFFubini proves the full approved geometric version in the recorded GammaGroundContext with the precise accepted Section 3 YinGammaGroundUnmeasuredLiftInput, alongside the full bounded theorem. NativeGeometricVFFubiniVanishing proves intrinsic geometric fibrewise vanishing and preservation under any ground comparison. Finite denominator witnesses precede preparation; actual affine padding, retained old RV coordinates and base-zero strata give common total-degree normalization. The finite RES display simplification, actual-variety/global-comparison corollary specialization and concrete Puiseux ACVF-model proof remain. No HK result is assumed.

Full audit 62 passed (Section5/.scratch/finite-comparison-audit-62.log): 1112 public definitions/structures and 1853 theorems, with only the standard Lean principles. RESFibreOnlyCriterion proves both directions of the exact finite stabilized criterion with only fibre pairs, one common positive stabilizer and an actual tagged bijection. Degree-forgetting pairs are absorbed without positive cancellation. Dean Cureton's Apache-2.0 Newton-Puiseux proof (commit 73e78681d7bb78ddb202e29cb92ab3c16b723126) compiles locally with proof bodies unchanged. PuiseuxAlgebraicClosedness identifies its field with the actual local bounded-denominator Hahn subfield. PuiseuxConcreteResidue, PuiseuxConcreteRVOperations and PuiseuxConcreteLanguage construct the actual residue-field and whole-language bridges; PuiseuxConcreteModel proves ACVF(0,0) with no model input. PuiseuxConcreteComparisons.theta_5_14_concrete is the actual comparison with that model hypothesis discharged. Both Fubini versions remain proved with the precise accepted Section 3 lifting/kernel input. The finite-variety-chart and saturated-ambient global-comparison specialization of the final corollary remains unfinished. Audit 61 failed only declaration discovery; corrected namespace prefixes and block-comment handling are included in this successful rerun.

## November 18 additions (pending extraction into Fubini-theorems)

These modules are owned by diamond-integral for now. They will be extracted
into Fubini-theorems and replaced here by compatibility imports, as for the
rest of Section 5. Details are in `GAP-REPAIRS.md`.

- Inflated-family Fubini and its Vol version: `InflatedFamilyFubini`,
  `InflatedFamilyFubiniVol`, with the `InflatedGamma*`, `InflatedRelative*`,
  `InflatedIntegerBlockReduction` and `InflatedGammaBasePartition` modules.
- Theorem 5.17 and Proposition 5.23 for RV[*] fibres: `WeakDegreeFubiniDischarged`.
- The ambient model for Vol and Corollary 5.21: `PuiseuxMonsterAmbient` (with
  κ-saturated, strongly homogeneous elementary extensions in ZFC).
- The ambient Θ is an isomorphism: `ElementaryRESExtensionData` and
  `ElementaryRESExtension`.
- Lemma 5.19 in polynomial form (`Lemma519Polynomial`) and Test 5.20 for tuples
  (`Test520Tuples`).
- Author-approved "not pursued": Remark 5.16, Remark 5.18's examples, and the
  global twist:C formula.
