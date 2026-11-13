# Numbered §3 targets

Reference: `section 2/reference/diamond_integral_revision_annotated.tex`
at project main `82fe1a1`, with its author-approved §2 revisions. Stable
labels below take precedence over page and printed theorem numbers.
The approved C002 proof is on printed pages 34–35. The author-approved R050, R051 and R053 corrections are applied; R054 is approved and applied.

| Target | Stable label | Status / next obligation |
| --- | --- | --- |
| Definition 3.1 | `def:Kgroup` | Generic positive additive scissors, groupification and universal properties; instantiated with real-base VF/RV groupoids. RV graded products and equivalence of the universal semiring presentation with the fixed-degree direct sum are proved; RES has graded products and an injective graded inclusion. Measured RV and measured RES also have proved direct-sum comparisons and an injective graded inclusion. The unmeasured VF filtered semiring has a proved categorical colimit comparison and injective dimension-bound inclusions. The measured VF direct-sum and cartesian-product semiring comparisons are proved relative to both accepted lift records. All four full Gamma-ground Gamma categories now have actual cartesian graded semirings, universal-presentation/direct-sum equivalences and group-completion gradings. |
| Definition 3.2 | unlabelled, immediately before `RV:fiber:dim:same` | Maximum of the actual §2 fibre dimensions, with bottom on empty sets; upper bounds and attainment checked at real bases. |
| Lemma 3.3 | `RV:fiber:dim:same` | Proved at small real bases and at the complete original Gamma ground by gammaGroundLemma_3_3, with canonical structure, saturation and characteristic zero explicit; RV exchange is discharged by the earlier theorem. |
| Definition 3.4 | `defn:VF:cat` | Real-base and complete-Gamma-ground groupoids are implemented with the §2 VF dimension and literal finite RV fibres. Topology is explicit. |
| Definition 3.5, Remark 3.7 | `defn:VF:mu:G`, `mor:equi` | Positive-degree essential representatives, quotient germs and groupoid are proved at real bases and over the complete Gamma ground, with the actual §2 smallness. The Gamma-ground comparison constructs pointwise preserving cofull representatives. Degree zero is a separate form-preserving genuine-bijection groupoid retaining all forms. The actual full-ground essential category and its dimension-agreement quotient are implemented. |
| Notation 3.6 | unlabelled | Explanatory Gamma-volume convention; no extra theorem. |
| Definition 3.8, Notation 3.9 | `defn:c:RV:cat`, `0coor` | Real-base and complete-Gamma-ground RV groupoids, finite-to-one **nonzero** target and unrestricted zero tags in the domain implemented. At Gamma ground, actual coproducts, positive representatives and equality exactly when a genuine same-ground isomorphism exists are proved. Exact finite zero-pattern stratification into nonzero targets in degrees at most the original degree is proved. Every object is isomorphic to a graph object whose label map is exactly the first coordinate projection. The actual VF[0]/RV[0] category equivalence is now proved at the complete original Gamma ground, using invariant finite VF coding; the measured degree-zero equivalence is proved with all forms retained. |
| Definition 3.10 | `defn:RES:cat` | Finite domain-value-support full subcategory defined. Scissors, coproduct representatives, class-isomorphism comparison, graded products and the injective graded inclusion into RV are proved at the real-base scope. At complete Gamma ground, product/coprod closure, fixed-degree representatives, class-isomorphism comparison, actual graded cartesian products and the injective positive graded inclusion are also proved. |
| Notation 3.11 | `mor:ftf` | The actual correspondence is a definable image, contained in the two label images, with finite fibres in both directions. Its nonempty finitary-function presentation and exact pointwise Jacobian abbreviation are proved at real bases. |
| Definition 3.12 | `defn:RV:mu` | Pointwise Gamma-measured RV groupoid and measured RES full subcategory implemented at a real base and over the complete Gamma ground. Gamma-ground RV/RES have actual coproducts, positive representatives, exact pointwise measured class-isomorphism comparisons, genuine graded cartesian semirings and an injective positive graded RES inclusion. Measured RV is equivalent to its universal presentation at this scope. Positive classes have genuine representatives, class equality is exactly measured isomorphism, both graded/direct-sum comparisons are proved, and measured RES injects into measured RV. |
| Definition 3.13 | `def:Ga:cat` | Finite tagged Gamma families and genuine definable RV contraction witnesses implemented at real bases and over the full Gamma ground, including the ordinary/measured groupoids and fixed-degree scissors. The full-ground coproducts, actual positive representatives and exact class-isomorphism comparison are proved, including finite Gamma and the injective positive finite-to-Gamma inclusion. Cartesian graded products and universal-presentation/direct-sum comparisons are proved at the complete Gamma ground, including finite Gamma and its injective positive graded inclusion. Actual coproducts and partitions retain full RV code witnesses; positive equality is exactly genuine isomorphism, and every positive class has an actual object representative. Actual products induce the graded semiring, equivalent to its universal presentation; finite Gamma has the corresponding comparison and injective inclusion. |
| Remark 3.14 | unlabelled | Compare divisible-hull definability with existence of an RV representative; do not identify them. |
| Remark 3.15 | `GLZ:char` | R050 approved and applied. Arbitrary full-code contractions from Gamma^n to Gamma^m are locally proved piecewise integer-affine, including nonbijective maps, rectangular matrices and zero arities. The finite-tagged piecewise-GL morphism criterion is also proved over the complete mixed ground, with actual definable RV translations and GammaGroundContext wrappers. The only new cited premise is the approved R--Y classification. The precise [19] record remains at its stated real VF-generated scope; it is not used for lower-map well-definedness. |
| Definition 3.16 | `def:Ga:cat:mu` | Measured Gamma groupoid and full piece forms are implemented at real bases and over the full Gamma ground. Actual coproducts, positive representatives and exact measured class-isomorphism comparison are also proved over the complete Gamma ground, including the finite measured subcategory and its injective positive inclusion. The real-base graded semiring/direct-sum equivalence is proved; the full-ground graded/presentation comparison and canonical tensor maps are proved; the corrected positive quotient comparison is now proved as well. Finite measured Gamma has the corresponding positive and graded comparisons and injective inclusion. |
| Notation 3.17 | `comp:form` | Both RV and Gamma combined weights and their pointwise measure equations are checked. |
| Ordinary coefficient square after Notation 3.17 | C002, unlabelled square | Both horizontal positive maps are now proved injective locally in each original degree and in the graded semirings, with actual Gamma-isomorphism reflection, all finite tags and full original-ground RV lifts. GammaGroundCoefficientMonicityContext specializes the full VF/Gamma context. The approved R--Y classification is the only additional cited input; well-definedness uses neither [19] nor R--Y. The complete 1,003-module integrated audit passes. No groupified injectivity is inferred. |
| Tensor maps / Proposition 3.18 | `bil:def`, `tensor:expre`, `bdd:to:2bdd`, `red:D:iso` | Both actual positive tensor maps are surjective. Both elementary coefficient-translation semiring congruences equal their actual kernels; both quotient maps are semiring isomorphisms with multiplicative fixed-degree direct-sum gradings and the original r+n object-degree formula. The actual groupified kernels are also exactly the ideals of these generator differences, with both quotient ring comparisons proved. These are local proofs with no HK input. TensorPresentationContext instantiates the corrected proposition at the actual VF/Gamma-generated GammaGroundContext, retaining canonical structure, ACVF00, saturation, both smallness bounds and nontrivial Gamma. General imaginary-ground presentation transport remains separate. The final T001 statement and both proofs are now author-approved and incorporated in the manuscript. |
| Notation 3.19 | `drop:0` | Constant additive volume 0 is multiplicative weight 1 in the Lean Gamma convention. |
| Notation 3.20 | unlabelled | Distinct elementary groupified relation identities checked. The actual unmeasured point and positive-value objects, their semiring congruence and the P−1 completion comparison are proved. Both actual measured and unmeasured generators, congruences and principal-ideal completion comparisons are now instantiated. The Gamma, measured Gamma and both finite Gamma graded comparisons and group-completion/direct-sum comparisons are proved. R051 spelling correction is approved and applied; its original referee note is gray. |
| Notation 3.21 | `RVcat:tag` | Both object lifts, including the measured form in every degree, are implemented at real bases and over the complete original Gamma ground. Class descent and surjectivity retain precise accepted [18] inputs at the manuscript's VF/Gamma-generated context. Independent imaginary names are outside the documented default context. |
| Theorem 3.22 | `main:prop:HK` | Actual positive and ring integral comparisons and characterizations are proved relative to precise accepted [18] inputs over a small VF-generated real base. Bounded unmeasured comparisons and transition compatibility are proved in that scope. The unmeasured VF colimit identifications in additive commutative monoids and in additive commutative groups are proved at that real-base scope. The measured VF direct-sum, product semiring and ring comparisons are also proved relative to both accepted lift records in that scope. Complete Gamma-ground positive/ring and fixed-degree measured integral consequences now have explicit accepted [18] inputs, and bounded unmeasured consequences retain actual finite direct sums and transition maps. The Gamma-ground measured VF direct-sum, product-semiring and group grading are proved relative to the accepted global/degreewise inputs. The ordinary Gamma-ground universal-semiring identification and its actual additive/group filtration colimits are proved relative to the accepted global/bounded inputs. The pure Gamma-ground RV/RES gradings are now proved. Gamma/finite-Gamma graded comparisons and the documented VF/Gamma-generated context applications are proved; geometric kernels remain precise cited inputs. R054 notation correction is approved and applied; its original referee note is gray. |

Additional Gamma-ground results now include the actual VF dimension and
finite-RV-fibre invariance, fixed-bound scissors and transitions, and the
categorical additive/group colimits of the dimension filtration. The
unbounded additive quotient in these colimits uses genuine Gamma-ground
bijections and cuts. Its comparison with the cartesian universal semiring and the latter’s actual
additive/group colimits are now proved relative to the accepted global and
bounded [18] inputs. Degree-zero measured VF is also implemented over this
ground. The positive-degree essential measured category has now also been
constructed at this scope: full same-ground derivative formulas and fibre
interiors give pointwise preserving cofull representatives, their quotient
has the exact manuscript-dimension agreement criterion, and the groupoid
and fixed-degree scissors are proved. The finite sorted syntax bridge now includes VF as well as RV coordinates,
with the proper-sort guards and every Gamma code retained. The current completion review below supersedes the historical open-item notes.

All §3 manuscript targets are now covered in the documented paper
contexts, relative to the explicitly accepted later [18] comparisons and
approved R--Y classification. This is a semantic review of actual types,
not an inference from export counts. The machine-readable current map is
`verification/paper-targets.json`; it links 21 manuscript targets to 119
audited declaration heads. The chronological entries below retain their
original milestone scopes and are superseded by the completion review.
No HK result is a given input. Independent disc names outside the default
paper context and concrete §4 categories are outside this certificate.


## Historical reuse checkpoint at 488 modules

The 488-module receipt includes the original-Gamma-ground RV dimension
and VF-fibre comparison, all 26 direct [18] proof exports, complete finite
DC-name syntax transport, and checked constructors for all eight legacy
interfaces of numbered [18, §3] results. Native 2.23, 2.25, 2.27, 2.28,
2.30 and 2.32 wrappers supply these constructors. The mixed 3.21 adapter
uses finite real support and four zero cells while retaining the original
Gamma base and all RV labels. Actual saturation at an infinite cardinal
remains explicit where used. The separate Gamma-affine background, later
[18] integral/kernel inputs and local tensor proof obligations remain distinguished.
See `verification/integration-reuse.json` and the latest entry in STATUS.md.

The author has now required local proofs of all HK coefficient/tensor
results; no HK input is authorized or pending approval. The former
conditional proposal is withdrawn. See `verification/HK-INPUT-REVIEW.md`.


## Local tensor surjectivity result

The concrete unmeasured positive tensor map and its group-completed map
now have local surjectivity proofs in `UnmeasuredTensorSurjectivity.lean`.
Their hypotheses are actual saturation at an infinite cardinal, ACVF00,
canonical structure, small original real/Gamma supports and nontrivial
Gamma definable closure of the original base. The proof has full original-
ground product charts on all RV tuples, including zeros, actual RV[k]
label-degree transport to RES[k-m], literal full Gamma fibre lifts and
finite positive-scissor assembly. The earlier rank inputs are furnished
by checked [18] adapters. No HK result is an input.

This does not certify Proposition 3.18: injectivity and the measured tensor
comparison, as well as the Gamma-to-RV coefficient embeddings, remain open.
The subsequent measured proof route is to descend Gamma-valued forms to
finite original-ground partial Gamma functions of the input value tuple,
then refine product residue factors by their finite value support.


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


### Critical tensor scope review, 2026-11-12

Generic-fibre affine monomial formulas with old-ground coefficients and
unimodularity for injective square maps are now checked in
`RVGenericFibreMonomials`. The complete 712-module build/audit passes.
The finite-coefficient descent needed for the stated tensor injectivity
has a mathematical counterexample under the manuscript's conventions;
see `verification/TENSOR-COEFFICIENT-OBSTRUCTION.md` and colored review T001.
Both tensor surjectivities remain proved. Proposition 3.18 and the overall
section are not marked complete. The working manuscript is unchanged.

### Unmeasured kernel: corrected mathematical target for review

The generating presentation and full mathematical proof are recorded in
`verification/TENSOR-KERNEL-PRESENTATION.md`. The generators are
[X]_r tensor ([U]_m-[U+delta e_i]_m) whenever a definable function
c:X -> delta^sharp exists over the original ground. Formal targets not
yet completed are: uniform RES-dependent monomial product neighbourhoods,
finite disjoint product covers of full-rank types, lower-rank normalization
with degree-preserving finite-Gamma balancing, and positive congruence
assembly. Groupification can then use the checked generic algebraic
comparison. A separate direct target is the degree-one torus annihilation
of every generator. These are replacement targets for mathematical review,
not a certification of the original injectivity statement. The measured
kernel remains separate.

### Measured kernel: mathematical presentation and formalization targets

`verification/MEASURED-TENSOR-KERNEL-PRESENTATION.md` now gives the separate
measured presentation. Its Gamma target form is
sigma_delta(eta)=sigma(eta-delta e_i)-delta. In addition to the common
monomial-neighbourhood/compactness/scissor work, formal targets include
the degree-zero shared weight-shift balancing p_a, transport of forms
through fixed-coordinate normalization, the canonical forgetful and
zero-combined-weight tensor maps, and the measured torus annihilation.
The explicit fifth-root measured kernel element maps under forgetting
forms to the existing nonzero ordinary element. This is a mathematical
nonvanishing proof, not a completed concrete Lean model. The original
Proposition 3.18 and the whole section are not certified complete.

### Unary unmeasured ring refinement

The author requested existential witness notation and a one-variable
Gamma generating family. The notation is corrected in the verification
notes. `verification/TENSOR-KERNEL-UNARY-GENERATORS.md` gives a
mathematical unary-ray ideal presentation. Formalizing that refinement
also needs the translation-compatible signed polyhedral cone expansion,
integral cone subdivision, and product-difference assembly. This is a
ring refinement of the full-coordinate target; a unary positive
congruence and a unary measured refinement have not been established by
the argument recorded here.

### P_Gamma priority check

`verification/P-GAMMA-PULLBACK.md` gives the direct commuting-diagram
proof that the full pullback of (P_Gamma), after forgetting forms and
passing to the full unmeasured tensor ring, lands in ker(Psi). Each
stipulated P_gamma has an explicit canonical tensor lift mapping to
zero, using its old-ground t_gamma and full tails. The RES evaluation
therefore kills the entire pullback, with no extra RES quotient. Future
concrete formalization must retain endpoints, the zero-radius case,
bounded/full distinctions, and both ideals in the bounded tensor
quotient. The extra bounded tensor kernel is not absorbed by the ideal
of canonical annular lifts; a bounded root example separates them.
The direct pullback argument does not require first finishing the full
kernel generation theorem.

### Positive semiring presentation is primary

For both tensor maps the author now requests surjectivity followed by
an explicit kernel congruence and a quotient inverse, before any
groupification. `TensorCoefficientRelations.lean` and
`MeasuredTensorCoefficientRelations.lean` check the elementary pairs
against actual product bijections and construct the surjective positive
quotient maps. `RVUnitCoordinateTuples.lean` checks the scalar versus
sparse-tuple coefficient condition. Original-ground neighbourhoods, local
monomial congruences, finite monomial covers, actual patch images, positive
disjoint product partition identities, finite hyperplane reduction and
the rank-zero base are checked. Both reverse kernel inclusions remain
targets: assemble the global finite matching and residual RV bijection,
complete rank induction, then retain the measured forms and degree-zero
weight shifts throughout the same comparison.

Ray-only pairs do not generate the positive kernel congruence: there
are distinct bounded tensors in the kernel, and a coarse positive
congruence containing every ray pair keeps such tensors distinct.
Retain general U in the primary target. No claim that every Gamma
arity is indispensable, or that bounded unary pairs suffice, is made.


The latest integrated checkpoint is 788 supporting modules plus Section
(2406 public theorem types; standard principles only). The actual finite
matching is checked on both sides of the RV bijection; matched sums are
congruent in the positive tensor and their image families are disjoint.
Three later individually checked modules supply the residual bijection,
positive residual partitions and smaller-rank native normal forms. The
residual tensor/RV presentation and final induction remain; neither
reverse kernel inclusion nor Proposition 3.18 is certified complete.


The next complete checkpoint is **794 supporting modules plus Section**
(2435 public theorem types; standard principles only). At explicit
canonical, saturated, small Gamma-ground scope, the full unmeasured
positive kernel equality and quotient semiring isomorphism are proved in
`UnmeasuredTensorPositiveKernel.lean`, by positive rank induction and total
degree reassembly. The measured reverse inclusion, the separate formal
graded quotient interface and full parameter-context translations remain.
Proposition 3.18 as a whole is not certified complete.


The 799-module complete receipt additionally supplies the unmeasured
positive quotient's multiplicative direct-sum grading and its r+n object
formula. It checks measured RES weight partitions and normalization via
shared finite measured Gamma scalars in degree zero. The full measured
reverse inclusion and complete parameter-context translations remain.


The 810-module complete receipt (2483 theorem types, standard principles
only) includes normalized finite single-piece forms for arbitrary positive
measured tensors and their weighted local monomial congruence, actual
measured native product charts, and finite labelled RES/Gamma partition
identities. The common Boolean-grid product partition theorem was checked
individually afterward. Global measured matching and induction remain.


2026-11-12, measured rank-layer checkpoint: 830 supporting modules plus
Section pass the complete build/declaration audit (2537 theorem types,
2104 definitions, 151 named instances, 8 reused heads). Actual weighted
rank-layer objects, two-sided local covers, source selection, inherited
residual atlases and positive weighted reassembly are now checked.
Remaining measured work is the weighted hyperplane reduction, rank
induction and full degree reassembly; complete context translations also
remain. The unmeasured graded quotient is already proved at explicit
Gamma-ground scope.


2026-11-12, both positive kernels: 842 supporting modules plus Section: 2566 theorem types, 2116 definitions, 151 named instances and 8 reused heads (4841 audited heads). Both measured and unmeasured complete positive kernel equalities,
quotient isomorphisms and graded object formulas are audited. The actual
GammaGroundContext wrappers are checked. General imaginary-ground transport
and other whole-section context obligations remain separate; final T001
adoption is approved and incorporated.


## Adopted manuscript, finite-name diagrams and positive descent — 2026-11-12

The integrated build and full declaration audit pass for **849 supporting modules plus Section: 2587 theorem types, 2134 definitions, 154 named instances and 8 reused heads (4883 audited heads)**,
with the adopted manuscript hash
24c58ba674814c3f12f6097b9fd61dc5675af627b6b9d4a43cae46052e6f68cb.
Only standard logical principles occur and all dependency pins are unchanged.

GammaGroundFiniteNameSupport gives common original-name support for finite
heterogeneous sets and full graphs. GammaGroundNamedFunctors preserves
actual VF, RV and measured RV maps faithfully. GammaGroundNameClosure proves
that already definable interpreted names add no definable sets or graphs,
while retaining every old Gamma name. GammaGroundMeasuredDiagramSupport
and GammaGroundVFDiagramSupport reconstruct finite diagrams literally,
including all measured RV labels and forms. No real RV representatives
are added to the ground.

PositiveTensorDescent proves the necessary-and-sufficient elementary-pair
criterion and uniqueness for descent to RV for both positive tensor maps.
BalancedTranslationDescent constructs the unique positive RV evaluation
from balanced coefficient maps and a numerically translation-invariant
Gamma evaluation; its restriction to RES is exactly the prescribed map.
This is an interface for the later Euler construction, not a claim that
the numerical Euler characteristics or section 4 balancing have been built.

The separate Gamma-to-RV and finite-Gamma-to-RES positive monomorphisms
in the prose coefficient square remain proof obligations. The actual
degree-zero VF/RV category equivalence is also not yet exported over the
complete Gamma ground; invariant finite VF coding is the next local step.
The updated verifier scope metadata records these concrete boundaries.
No new manuscript review is pending, and no commit or push has been made.


## Actual degree-zero comparisons — 2026-11-12

The integrated build and complete declaration audit pass for **860 supporting
modules plus Section: 2605 theorem types, 2150 definitions, 158 named
instances and 8 reused heads (4921 audited heads)**. Only standard logical
principles occur. The adopted manuscript and dependency pins are unchanged.

`BoundedVFFibreCoding`, `GammaVFCoordinateRows`, `GammaFiniteVFCodeGraphs`
and `GammaFiniteVFCoding` give uniform finite VF codes whose entire graphs
are invariant under every representative of the original Gamma names.
`GammaGroundFiniteVFCodeMaps` turns those graphs into actual definable
injections; `GammaGroundFiniteMixedCoding` retains existing RV coordinates
and codes finite mixed domains over that same ground.

`GammaGroundVFZeroFiniteness` proves intrinsic finiteness of every ordinary
VF[0] domain. `GammaGroundZeroRVLift` and
`GammaGroundZeroCategoryEquivalence` prove the actual ordinary category
equivalence using the manuscript's object lift, full faithfulness and
essential surjectivity. Canonical structure, ACVF00, saturation, small real
base and the valuation-topology compatibility remain explicit. Temporary
Gamma-code realization is used only to prove intrinsic finiteness, never
to descend a map defined over an expanded real base.

`GammaGroundZeroMeasuredLift` and `GammaGroundZeroMeasuredEquivalence`
prove the measured degree-zero category equivalence with every original
Gamma form retained pointwise. The measured domains already have no VF
coordinates, so this equivalence needs no extra coding or saturation
hypotheses. No HK premise, cancellation or groupification is involved.

The separate Gamma-to-RV and finite-Gamma-to-RES positive monomorphisms
remain unfinished. Both positive tensor quotient presentations are already
proved and adopted; the coefficient embeddings are being checked directly.
No manuscript review is pending, and no commit or push has been made.


## Annular compatibility and the coefficient proof question — 2026-11-12

The integrated build and complete declaration audit pass for **873 supporting
modules plus Section: 2620 theorem types, 2172 definitions, 158 named
instances and 8 reused heads (4958 audited heads)**. Only standard logical
principles occur. The adopted manuscript hash remains
24c58ba674814c3f12f6097b9fd61dc5675af627b6b9d4a43cae46052e6f68cb;
the dependency pins are unchanged.

`GammaGroundRVFamilyReflection` reflects arbitrary bijections of actual RV
family realizations to complete definable family graphs.
`GammaGroundGammaLiftReflection` transports those bijections to full code
families and proves descent when the decoding equivalence is preserved and
reflected. It proves the Gamma-to-RV positive injection in degree zero and
reflection for singleton Gamma domains in every arity, including values
without definable RV representatives. It does not prove reflection for all
finite Gamma unions or all Gamma objects.

`GammaGroundConstants`, `FullGammaFunctionOrder` and
`GammaGroundPointTranslations` construct actual old-ground multiplier maps.
`GammaGroundTails` and `GammaGroundAnnulusAbsorption` prove the positive tail
decomposition and absorption of the half-open annulus (0,delta], including
the zero-radius case. `GammaGroundAnnulusRingVanishing` derives zero only
after additive completion in the full unbounded Gamma and RV rings.
`GammaGroundDefinablePoints` supplies the actual singleton bijections.
`GammaGroundMeasuredRVForgetting` constructs the positive and ring
forgetful homomorphisms on actual objects and full forms.
`GammaGroundAnnularForgetting` proves the corresponding stipulated annular
expressions vanish after forgetting forms.

`IdealPullbackKernel` and `GammaGroundAnnularPullback` prove annihilation of
their entire generated ideal and its full pullback into the actual
unmeasured tensor kernel for every commuting presentation. The latter
retains the presentation maps and their commutation equation as explicit
arguments. The concrete bounded categories and comparison maps from
section 4 have not been constructed; this is not a certification of the
whole bounded diagram or of numerical Euler characteristics.

C001 is the critical remaining coefficient-embedding proof question:
from a same-ground RV bijection I-sharp ≃ J-sharp, construct a same-ground
Gamma bijection and some fibre-respecting replacement RV bijection, with
all finite tags retained. An arbitrary supplied RV bijection need not
itself contract. Neither the corrected tensor quotient theorem nor the
checked descent criterion constructs this replacement. The finite Gamma
case without definable RV representatives is part of the open obligation.
No counterexample or mathematical error in the coefficient embedding is
asserted, and no HK input is being requested or assumed.

The proof question is blue inside the unchanged manuscript context on
printed pages 33–34 of `reference/proposed-revisions/C001-coefficient-embedding-question.pdf`.
The PDF-only right-panel request returned queued; visibility is unconfirmed.
The working manuscript is unchanged, and no commit or push has been made.


## Coefficient-map scope correction — 2026-11-12

The lower horizontal map is checked for the explicit full-preimage
category encoded by `GammaHom` and `GammaGroundGammaHom`. Its comparison
with an interpretation of Definition 3.13 allowing contractions of
bijections between arbitrary RV subsets was not established. Under that
weaker interpretation, the fifth-root example over C((t)) separates equal
Gamma singleton classes whose full RV fibres are not definably bijective;
well-definedness itself fails. The model and curve argument are a
mathematical audit, not a newly compiled Lean model construction. See
`verification/COEFFICIENT-MAP-SCOPE-AUDIT.md` for the proof and the exact
scope of the reference to Lemma 2.29.

For the full-preimage definition, horizontal injectivity remains an open
local proof obligation: no counterexample to it has been established.
The new review batch C001/C002 proposes making that definition explicit
and provisionally omitting horizontal monicity; the latter is withdrawal
of an unsupported assertion, not a claim that it is false. The previous
C001 proof-question PDF is preserved. Both new proposals require author
review, and the approved manuscript is unchanged. The updated integrated
audit passes with the existing 873 supporting modules and 2620 theorem
types; this scope correction does not add Lean results.


## Author clarification: intended Gamma morphisms — 2026-11-12

The author confirms the intended Gamma-morphism convention: the witnessing
bijection is on the full RV preimages. The arbitrary-RV-subset alternative
was introduced by the assistant and is not the category under discussion.
C001's proposed definition correction is withdrawn. Its mathematical
counterexample concerns that alternative only and provides no evidence
against monicity of the intended lower horizontal map. For the intended
category, well-definedness is checked; general horizontal injectivity
remains unresolved. C002's provisional omission of the assertion has not
been approved, and the main manuscript remains unchanged. The existing
C001/C002 PDF is retained as history and includes a withdrawn item.


## Positive monicity: mathematical proof and dependency check — 2026-11-12

A mathematical proof of the intended positive Gamma-to-RV monomorphism
was found. It extracts the unique residue-generic fibre match of an
arbitrary RV bijection, uses the original-ground RV twisting character
group, and applies Reichstein--Youssin Theorem 7.1 / Corollary 2.5 to
replace the equivariant birational match by a full monomial torus
isomorphism. Compactness glues finitely many such replacements. The upper
positive coefficient injection follows from the square and the checked
vertical injections. See `verification/COEFFICIENT-MONICITY-CHECK.md` for
the hypotheses, descent argument and source.

This is a mathematical proof using an external birational theorem, not
a completed local Lean proof. That external theorem is outside the
author-accepted input list and has not been added as a premise. No
groupified injectivity is inferred. There are no new supporting Lean
result modules or completed numbered formalizations in this update.

Horizontal monicity is unnecessary for the later constructions. The
manuscript dependency audit covers sections 3--8; all uses need the
horizontal homomorphisms, corrected quotient presentation and appropriate
descent checks. In particular Psi inverse and its bounded counterpart
need the quotient formulation already required by corrected 3.18. The
piecewise h_m maps retain separate lattice/descent obligations.
`verification/CoefficientDependencies.lean` also traverses the actual
compiled declaration closures of seven existing tensor, descent and
annular-pullback roots. It passes without horizontal injectivity; the
checked vertical RES-to-RV injection is used. The log and a separate
dependency receipt are retained in `verification/`.

C001 is withdrawn. C002 now presents the proof and its later role, with
no proposed definition change or assertion that monicity is false. The
blue manuscript-context review is
`reference/proposed-revisions/C002-monicity-and-use-review.pdf`, printed
pages 34--35. No manuscript edit or new external Lean input is adopted.


## November 12: C002 approved and local birational proof bridges

The author approved adding the proof and the published Reichstein–Youssin
citation. C002 is incorporated in black, with a green author resolution;
there is no matching referee item. The manuscript source SHA is
`080b909692985183f5e60db787e800dd23dd9c3b3bca01f7b1beb6efcc065b97`.
The resolved manuscript PDF is
`reference/proposed-revisions/C002-resolved-review.pdf`, pp. 34–35.
Its PDF-only right-panel request returned queued; visibility is unconfirmed.
C001 remains withdrawn. Earlier entries saying C002 or the cited input is
unapproved are historical and superseded by this entry.

The exact characteristic-zero diagonal-action classification is now the
explicit replaceable `ReichsteinYoussinInput`; no HK premise is accepted.
Local Lean proofs construct polynomial/rational diagonal actions, prove
faithfulness from joint weight generation and birational equivariance,
extend characters into algebraically closed field units, and recover
actual old-ground definable RV coefficients from equality modulo their
value subgroup. The resulting unimodular maps are full-fibre maps.

The pure-field bridge is checked locally: definable closure in ACF0 is
the parameter field; partial definable graph outputs lie in the field
generated by the inputs; a two-sided functional relation identifies those
fields and preserves independence of equal-length tuples. Their rational
function field isomorphism intertwines any diagonal action preserving the
graph. Formula transport uses the checked ACF QE proof and an intermediate
field embedding, without requiring an ambient automorphism. The cited
classification is applied only after these local constructions.

Countably many algebraically closed coefficients can be chosen inside the
same residue field. Genuine saturation supplies independent residue tuples
over such a countable field. Actual original-Gamma-ground RV relations
normalize to pure residue-field relations without adding the normalizing
representatives to the final ground. The character twist fixes residue
points and original-ground RV points, preserves values and the named total
residue operations, and respects all well-sorted terms and formulas via
the released ACVF QE theorem.

This is supporting formalization, not completion of all-degree horizontal
monicity or the whole section. Finite generic-fibre matching, its uniform
original-ground definability and finite gluing still need local proofs.
No groupified injectivity is inferred. The later constructions do not use
horizontal monicity; the earlier dependency receipt remains applicable.
The complete audit must be rerun after the current additions before its
receipt covers this update.

The complete original-ground character-symmetry bridge now checks:
`GammaGroundCharacterSymmetry.rvCharacterTwist_definableOverBase` removes
all moved Gamma representatives by their invariant full code preimages;
`GammaGroundRVMapCharacterSymmetry.gammaGroundRVMap_character_equivariant`
applies it to actual map graphs. This introduces no extra names, no HK
input, no ambient VF automorphism and no saturation hypothesis. The
remaining monicity obligations are generic-fibre matching, its uniform
original-ground definability and finite gluing.


### Integrated C002 bridge audit

The 904-supporting-module checkpoint passed the complete project build
(11,389 Lake jobs) and declaration audit: 2,692 theorem types, 2,199
printed definitions, 158 named instances and eight reused declarations,
5,057 declarations in total. Only `propext`, `Classical.choice` and
`Quot.sound` occur. The receipt pins the approved C002 manuscript SHA
`080b909692985183f5e60db787e800dd23dd9c3b3bca01f7b1beb6efcc065b97`.
Further generic-fibre modules added after this checkpoint require the
next integrated receipt. No complete all-degree monicity claim is made.


### Uniform generic selector and finite partitions

The local generic-selector bridge now proves uniform definability over the
complete original Gamma ground, full value-fibre invariance, and agreement
with membership at an actual independent residue tuple. Finite families of
all intermediate selectors have one countable algebraically closed residue
coefficient field; saturation supplies a simultaneous test tuple.
`rvFullFibreGeneric_partition` then proves exactly one generic part in any
finite definable partition of a full RV fibre. These are explicit actual
RV sets and full value-code relations, not additional geometric inputs.

The general horizontal monomorphism is still unfinished in Lean: the next
step matches an actual RV bijection and its inverse using these selectors,
then uses the proved character symmetries and the approved diagonal-action
classification to obtain old-ground full-fibre monomial maps and glue them.
The previous 904-module audit is superseded only when the new integrated
receipt completes. The mathematical C002 proof and PDF remain adopted.


### Integrated generic-selector audit

The complete 921-supporting-module checkpoint passes (11,406 Lake jobs):
2,725 theorem types, 2,207 printed definitions, 158 named instances and
eight reused declarations; 5,098 declarations audited in total. Only
`propext`, `Classical.choice` and `Quot.sound` occur. The integrated receipt
includes every generic-selector, common-coefficient, simultaneous-test-point
and finite-partition theorem described above. It still does not certify
all-degree horizontal monicity. The approved C002 manuscript SHA is unchanged.


The next local bridge is now connected to actual maps: the full value
graph of an RV map, retaining every output value representative, produces
an original-ground definable Gamma relation via the generic selector.
`rvNormalizedMapRelation_pure` extracts the pure-field graph from the
actual original-ground map. Its forward and inverse functionality are
proved, and characters of an injectively embedded weight group extend to
the original value quotient and preserve that actual normalized graph.
These additions postdate the 921-module receipt. Functionality and
bijectivity of the resulting Gamma relation for full RV-preimage
bijections, followed by finite gluing of the classified monomials, remain
unfinished; no general monicity theorem has been reported complete.


### Actual generic contraction and original-ground weights

`gammaGroundRVGeneric_contraction` now constructs the actual interpreted
Gamma map for a map from full RV preimages, retaining the complete original
real/Gamma ground and its actual target. Scalar generic values are unique,
and finite coordinate assembly includes the empty tuple case.
`gammaGroundRVGeneric_inverse_at` proves the inverse identity using one
locally constructed countable algebraically closed residue coefficient
field for the forward graph and all intermediate source/inverse selectors.
`gammaGroundRVBijection_generic_bijection` therefore supplies a genuine
interpreted Gamma bijection from a bijection of single full preimages.
These extraction and inverse results use no R--Y classification input.

`gammaGroundRVGeneric_original_coefficients` then applies the precise
approved R--Y input to the actual generic graph. Its conclusion has a
unimodular integer matrix and actual original-ground definable RV
coefficients at each Gamma point, with the weight group constructed from
the exact quotient by definable RV values. The interpreted generic
bijection has not yet been given a globally bijective full RV lift.
Finite formula selection/gluing, finite tagged families and general
positive horizontal monicity remain unfinished. All additions in this
entry postdate the 921-module integrated receipt.


### Integrated actual generic-bijection checkpoint

The 953-supporting-module checkpoint passes the complete project build
(11,438 Lake jobs) and audit: 2,777 public theorem types, 2,230 printed
definitions, 158 named instances and eight reused declarations, totaling
5,173 audited declarations. Only `propext`, `Classical.choice` and
`Quot.sound` occur. The receipt now includes the actual generic Gamma
bijection for single full RV preimages, original-ground pointwise
unimodular coefficients, finite map gluing, ordered cover refinement and
definable monomial agreement predicates. The original C002 manuscript
SHA is unchanged. General positive horizontal monicity remains unfinished;
finite formula extraction/gluing to a full RV bijection and finite
tagged families are the next obligations.


### Single-piece full lift and positive reflection

`gammaGroundAffine_partition_full_lift` now glues the finite old-ground
unimodular formulas into an actual bijection on the entire RV preimages.
It contracts pointwise to the interpreted Gamma bijection, including
arity zero and empty pieces. Injectivity uses the unimodular inverse;
surjectivity solves on each full value fibre.
`gammaGroundGammaSingle_reflects_RV_bijection` and
`gammaGroundGammaSemiringClass_single_eq_of_RV_bijection` therefore prove
actual Gamma-category isomorphism and equality already in the positive
semiring for single Gamma pieces. Their only new cited premise is the
approved R--Y classification. No cancellation or group completion is used.
Finite tagged family reflection remains unfinished, so this is not yet
general horizontal semiring injectivity. These additions postdate the
953-module integrated receipt.


### C002: general positive monicity proved locally

`gammaGroundUnitFamily_generic_bijection` constructs a genuine interpreted
Gamma-family bijection from an actual full RV family bijection, retaining
every finite tag. Its inverse compatibility is proved using one locally
constructed residue coefficient field for the actual partial branch graph
and both generic selectors. This extraction uses no R--Y input.
`gammaGroundUnitFamily_generic_original_coefficients` then applies only
the approved diagonal classification to obtain actual original-ground
RV coefficients and unimodular matrices at every Gamma point.

`gammaGroundUnitFamily_affine_full_lift` uses compactness and genuine
source/target branch partitions to construct a full bijective RV family
lift. Unit/code transport retains all representatives. Consequently
`gammaGroundGamma_reflects_RV_lift_bijection` proves actual Gamma-category
isomorphism reflection, and `gammaGroundGammaToRVKPlus_injective` proves
positive homogeneous injectivity. The checked direct-sum grading gives
`gammaGroundGammaToRVSemiring_injective`; the commuting square gives
`gammaGroundFiniteGammaToRESSemiring_injective`. Fixed-degree finite-Gamma
to RES injectivity is also proved. No cancellation or group completion
is used, and no groupified injectivity is inferred.

The only additional cited input is the precise approved R--Y consequence.
No HK result and no [19] classification input is used for well-definedness
or for this local ACVF proof. These additions postdate the 953-module
integrated receipt; the next complete audit is pending.


### Integrated C002 monicity checkpoint

The complete 977-supporting-module build passes (11,462 Lake jobs). The
full audit checks 2,815 public theorem types, 2,245 printed definitions,
158 named instances and eight reused declarations: 5,226 declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur. Both ordinary
horizontal positive coefficient monomorphisms are now included in the
integrated receipt, in each homogeneous degree and on the graded
semirings, with the actual GammaGroundContext wrappers. The approved
C002 manuscript SHA remains unchanged. This closes the local C002
monicity obligation, including finite tags and full original-ground
RV lifts, relative only to the expressly approved R--Y classification.
It does not certify the whole section or any groupified injectivity.
The next scope check concerns the broader-ground affine classification.


### Full-ground Gamma piecewise-GL classification

`gammaGroundGammaHom_iff_piecewiseGLZ` now proves both directions of
Remark 3.15's morphism criterion over the complete original mixed ground,
with finite source/target tags and actual definable RV translations. The
forward direction applies the proved generic coefficient construction to
the given morphism's own full code witness. The reverse direction glues
full RV bijections and uses no classification input.
`gammaGroundContext_GammaHom_iff_piecewiseGLZ` instantiates the actual
VF/Gamma-generated context; this is a local proof relative to the already
approved R--Y input, rather than a broader-base use of [19]. The separate
unary, potentially nonbijective contraction statement is still being
worked on; the accepted [19] record is retained at its stated real-base
scope. Well-definedness of the lower coefficient arrow remains the
independent direct proof from the full-preimage definition.

The full 982-supporting-module checkpoint passes (11,467 Lake jobs):
2,824 theorem types, 2,246 printed definitions, 158 named instances and
eight reused declarations, totaling 5,236 audited declarations. Only the
standard logical principles occur. No manuscript edit, commit or push
was made for this extension.


### Full-ground unary contraction classification

`gammaGroundUnary_code_contraction_piecewiseIntegralAffine` proves the
first sentence of Remark 3.15 for an actual map on full RV code preimages,
without assuming the RV map or its Gamma contraction is bijective. Its
finite partition has integer slopes and genuine original-ground definable
RV shifts. The proof stabilizes the RV map by `(u,v) -> (u,f(u)v)`,
classifies this genuine Gamma morphism in degree two and restricts its
finite affine formulas to the identity slice. All product, descent and
restriction graphs retain the original mixed base.

`gammaGroundContext_unary_contraction_piecewiseIntegralAffine` supplies
the actual VF/Gamma-generated context. Together with
`gammaGroundContext_GammaHom_iff_piecewiseGLZ`, both statements of Remark
3.15 have local full-ground proofs relative to the already approved
R--Y classification. No [19] statement is silently extended beyond its
stated base. The older precise [19] record is retained for reuse.
These changes postdate the 982-module audit and await the next full
integrated check. The manuscript remains unchanged.


## Final tuple classification and completion check — 2026-11-12

`gammaGround_code_contraction_piecewiseIntegralAffine` proves the first
sentence of Remark 3.15 for arbitrary actual full-code contractions from
Gamma^n to Gamma^m, including nonbijective maps and zero arities. Its finite
partition has rectangular integer matrices and genuine original-ground
definable RV shifts. The proof stabilizes to the full RV shear in degree
n+m, applies the checked full-ground morphism classification, and restricts
to the identity slice. The context wrapper retains the actual manuscript
VF/Gamma-generated ground. Only the already approved R--Y classification
is used as an additional cited input; [19] is not broadened.

The full project build and principle audit pass (11,483 Lake jobs), across
998 supporting modules plus Section: 2,843 theorem types, 2,254 definitions,
158 named instances and eight reused declarations, totaling 5,263. Only
`propext`, `Classical.choice` and `Quot.sound` occur. The verified semantic
coverage record links 21 manuscript targets to 115 actual declarations.
This completes the documented §3 paper contexts relative to the explicitly
accepted later [18] inputs and approved R--Y theorem, with no HK input.
Independent disc-name extensions and concrete §4 constructions are outside
this certificate. No groupified monicity is inferred from positive monicity.

Well-definedness of the lower coefficient map remains the separate direct
proof from full RV lift witnesses, with local scissors and product descent;
it needs neither [19] nor R--Y. The approved manuscript is unchanged
(SHA256 080b909692985183f5e60db787e800dd23dd9c3b3bca01f7b1beb6efcc065b97).
No commit or push has been made.


## Checked ring continuation — 2026-11-12

The full integrated project build and declaration audit pass (11,487 Lake
jobs), with 1,002 supporting modules plus Section. The receipt covers
2,866 theorem types, 2,270 definitions, 170 named instances and eight reused
declarations, totaling 5,314. Only `propext`, `Classical.choice` and
`Quot.sound` occur. It validates 119 declaration links for the 21 manuscript
targets. Counts report supporting infrastructure, not additional numbered
paper theorems.

Both actual ring tensor kernels now equal the ideals generated by the
explicit positive coefficient-pair differences. Both quotient ring
comparisons are instantiated in GammaGroundContext. Ring evaluation descent
is characterized by the same displayed pairs, with construction, image
formula and uniqueness proved. The full annular pullback lands in the
explicit unmeasured relation ideal for every commuting presentation.
These are local consequences of the already proved positive presentations;
no new cited premise, cancellation or embedding into group completion is
used. They complete the concrete groupification consequences of the §3
presentation. Actual Gamma Euler characteristics and concrete bounded §4
categories are separate §4 work. The supplementary signed unary-cone
refinement and diagnostic detector examples are not claimed as Lean exports
by this section certificate.

The §3 manuscript targets are covered in the documented paper contexts,
relative to the accepted later [18] lift/kernel records and approved R--Y
classification. No HK result is a given input. The manuscript hash remains
080b909692985183f5e60db787e800dd23dd9c3b3bca01f7b1beb6efcc065b97.
No commit or push was made. The approved PDF-only right-panel display
request returned queued; visibility was not asserted.


## [18] refresh and push authorization — 2026-11-12

The author explicitly skips the supplementary unary-ray refinement and
requests an upstream check, complete audit and push. The dependency is now
pinned at 7d4acc730496b3bd05a22c268ffd89540ca694f9. The previously reused
section 2–3 files are unchanged. Section 4 is checked and section 6 now
supplies finite RV integration, kernel and principal-ideal proofs relative
to its explicit unfinished section 5.8 input. Section 7 measured integration
is not available.

IntegrationLaterExports links ten exact section 6 declarations; their full
types retain Section5TwoOrderInputAll, native finite RV/VF categories and
VFGammaGeneratedBase. The last condition explicitly requires definable
closure of the generating base. GammaGroundContext records a generated
real substructure and a Gamma subgroup, without that closure equation.
The existing lift-input records therefore remain explicit until both the
closure transport and native/consumer category comparisons are compiled.
No legacy input is silently claimed discharged by an export alias.

The already approved proper-open-radius compatibility patch covers nine
dependency files. Numbered statements are unchanged; two auxiliary obstacle
premises now use proper OpenRadius, matching their corrected predecessor
producers. Other edits are confined to proof bodies. The patch, auxiliary
API changes, file hashes and base revision are recorded explicitly. CI now
prepares both dependency patches and runs both section audits.

The main branch's independent section 2 citation update was fast-forwarded
and reconciled with this work. The approved manuscript remains unchanged.
Both combined section audits passed before the authorized push to origin/main.


## Verified upstream refresh prepared for publication — 2026-11-12

Both section audits pass at the pinned Lean 4.35.0 toolchain. Section 2
retains 850 theorem exports and 378 selected reuse declarations. Section 3
checks 2,866 theorem types, 2,280 definitions, 170 named instances and eight
reused declarations: 5,324 heads across 1,003 supporting modules plus Section.
The receipt validates 36 native [18] export links and the 21 manuscript
targets with 119 declaration links. Only the permitted standard logical
principles occur. Both compatibility patches also apply to their clean
dependency indexes.

The native section 6 theorem types retain the unfinished Section5TwoOrderInputAll
and exact generated-closure/category conditions. Legacy lift/kernel records
remain explicit pending the checked comparisons; section 7 measured inputs
are not claimed discharged. No HK input or manuscript change is introduced.
The author explicitly skips the unary-ray refinement. CI now prepares both
patches and audits both sections, with the same 180-minute build allowance
as the upstream project. This record reports local verification; CI is
reported separately after publication.
