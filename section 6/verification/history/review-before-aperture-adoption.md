# Section 6 working record

## Source and workflow

The repository is `daviddhilbert/diamond-integral` at
`d4b6b059cf9c6b859603064c127b1275f42d977e`, cloned into `worktree/`.
The common manuscript is `section 2/reference/diamond_integral_revision_annotated.tex`.
The unchanged baseline is retained in `reference/baseline.d4b6b05.tex`.
No changes were made to the concurrent Section 5 working sources.

The Section 2–4 chat histories and current upstream working instructions
were read. The original Section 6 target remains independent of the
current Section 5 work. Clear corrections are applied directly under the
author's November 13 instruction. Critical mathematical scope changes
remain for author review. No commit or push is authorized by this chat.

## Manuscript changes

The exact applied changes and retained gray referee text are in the
manuscript and `reference/applied-manuscript.patch`. The independently
checked corrections are recorded in `reference/obvious-edits.json`:

| Item | Applied correction |
| --- | --- |
| R098 | Retain global bounds; treat the empty tuple as a singleton; specify membership-relation bounds for powerset-valued data. |
| R099 | Prove that the RV-hull preserves invariance, values, bounds, and existing tags before taking the complement. |
| R100 | Keep source partition balls in the current graph-fiber domain; justify local constancy of the recovered input tag. |
| R101 | Increase to an attainable radius and distinguish the contracted preparation from its tagged translation lift. |
| R103 | Deduce relation preparation from simultaneous preparation of all occurring VF-polynomials. |
| R104 | Require the product-domain condition for every use of FMT. |
| R105 | Use Boolean atoms of projected pieces, retaining all original pieces over each atom. |
| R110 | Correct sentence-ending punctuation. |
| R170 | Remove the finite-RV-fiber claim for the auxiliary hull complement. |
| R111 | Assume continuity explicitly in the standard-contraction setup. |
| R114 | Give the intermediate volume form and degree padding explicitly. |
| R115 | Construct centers over the full VF input, average finite families, and replace the whole exceptional RV-preimage by induction. The proof also records continuous branches for later use. |

These are manuscript-level corrections. Their application does not
certify that the corresponding full Lean results have been implemented.
The preparation induction (R106–R109), deferred-base construction (R112), continuous measured lifting (R116), and paired-disc volume calculation (R117) have also been written out in the manuscript. The preparation, deferred-base and measured-lifting constructions are now fully checked in the scopes recorded below. The full unary matching construction behind R117 remains unfinished.

The updated full manuscript compiles with Tectonic. For local rendering,
the scratch copy loads Latin Modern because the migrated default TeX
font cache was incomplete; this does not modify the manuscript's preamble.
The log has no Section 6 overfull boxes. The only overfull warning is the
pre-existing Section 2 line at 1406. The separately delivered R102 review
has two pages, no overfull boxes, and was rendered and visually inspected.

## Approved decision: R102

On November 13 the author approved the almost-everywhere repair. Lemma
6.14 now asserts total differentiability and Jacobian one off an original-base
definable set of VF-dimension less than the VF arity. The same convention
is adopted for standard contractions and their lifts. Exceptional sets
are pulled back along prefix bijections and united before using the total
chain rule. The original counterexample and referee text are retained in gray.

The resolved context PDF is `../output/pdf/section6-R102-resolved.pdf`;
the full revised Section 6 is `../output/pdf/section6-revised.pdf`.
Both were rendered and visually inspected. The right-panel requests returned
`queued`; no visible-panel state was observed. The latest full master build
places Section 6 on pages 59–80, with the opening of Section 7 sharing page 80.
No Section 7 source was edited. The downstream R126 fiberwise measure
warning remains to be handled by Section 7's own argument.

## Lean results and precise scopes

The checked entry point is `DiamondIntegral.Section6` through
`worktree/section 6/Section.lean`.

**Complete numbered result: Lemma 6.6 (`int:inv`).**
`DiamondIntegral.Section6.lemma_6_6` proves proper invariance of
`A ∩ B`, `rvHull A \ A`, and `B \ A`. Its `ProperInvariant S A`
interface includes original-base definability in the real mixed-sort
presentation, the global VF and RV bounds, and finite Gamma radii whose
full RV preimages are definable over `S` plus the existing RV tags.
The proof of hull definability is an existential formula over the
original base. The same radii work for the hull; coordinatewise maxima
for Boolean operations introduce no new names. The result only needs
ACVF and is therefore stronger than the characteristic-zero standing
scope. It makes no finite-RV-fiber assertion.

**Supporting foundations.** `QuotientCovariance` and `Covariance`
construct the actual quotient by open additive balls, prove the
factorization criterion, handle zero arity, and prove radius refinement
and Boolean closure. The Gamma order is the paper's order as supplied
by the pinned library; multiplicative notation represents addition
of valuations. A ball quotient is not identified with an RV quotient.

**Checked R170 obstruction.** `HullFiniteFibers` uses actual VF and RV
sorts, with `1 < δ` in multiplicative Gamma notation. It proves the
interval support infinite, the graph's RV fibers finite, proper invariant
geometry with a single radius, the exact RV-hull, and an infinite fiber
of its complement over VF coordinate `1`. The remaining definability
packaging of this particular example is not claimed as a new category
theorem; the set and its radius are given by the displayed original
formulas with parameter δ.

The audit checks every public declaration's full type and logical
dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` are
allowed; no `sorry`, extra axiom, unsafe declaration, or new HK input is
present. The receipt pins Lean 4.35.0 and all manifest revisions. The
existing approved dependency compatibility patches are prepared and
checked by the unchanged Section 2 and Section 3 scripts.

## Additional checked results

**Complete numbered result: Lemma 6.5 (`inv:crit`).** The least interior
radius is constrained to be at least zero (multiplicative one), including
full and zero-dimensional fibers. Its full proper-code graph is defined
over the original base. The radius is constant on each of its own balls.
The checked pure-VF Lemma 2.53 bounds this partition on a closed bounded
fiber; its definable supremum gives a radius definable over precisely the
original base plus the existing RV-tags. Empty fibers and zero arity are
included. No saturation or generation hypothesis is silently dropped:
canonicality, ACVF(0,0), genuine saturation above aleph-zero, and compatible
valued topology are explicit in the final type.

**Approved Jacobian repair, supporting local results.** Actual total
derivatives of coordinate shears have determinant one. Their definable
local charts are totally differentiable with determinant one off an
original-base definable VF-small set. The composed result retains finite
fibers, genuine saturation, smallness, and the canonical model exactly
where used. Finite composition removes prefix pullbacks of exceptional
sets. The concrete proper special-bijection constructors and their chart
adapters are implemented in the full numbered Lemma 6.14, recorded below.

**Preparation and matching support.** `ApertureRelease` proves the full
set factorization on a released annulus under the original invariance
radius, and saturation of the free coordinate. `DiscVolumeComparison`
uses the pinned Integration in ACVF `ConstructedGaussGraph.acvf_graph_input`
to discharge the predecessor's graph premise and proves constant-value
Jacobian descent on actual RV polydiscs, including the unary radius ratio.
No universal finite-extension reference, additional mathematical input,
or HK theorem is assumed. This is the local comparison in unary matching,
the volume comparison used in matching. The unary preparation construction is now complete; unary matching remains unfinished.

The expanded audit passed **1179** complete public declaration types and
transitive axiom checks with only the three standard logical principles.
The declaration count is evidence for this listed scope, not Section 6
completion. The exact current hashes and pins are in `verification/status.json`.

## Remaining work

Section 6 is not complete. Full unary matching (6.38) is the remaining formal target; measured preparation and standard contractions are now complete in every positive VF dimension, with arbitrary RV dimension and the standing hypotheses recorded below. Proposition 6.19 is complete in every VF arity and arbitrary RV dimension. Full positive-degree RV morphism factorization (6.29), all-degree RV Jacobian lifting (6.31), and positive-degree relatively unary measured VF chain lifting (6.33) are now constructed under their documented field-base and standing hypotheses. The literal-unary finitary lifting Lemma6.30 is complete. The manuscript proof expansions are applied; their
formal construction adapters are not replaced by unproved assumptions.
Lemmas 6.7–6.9 are now fully implemented and audited. The precise proper
covariance interface retains global source/image bounds and radius names
over all fixed source and target RV-tags. A continuous definable map on a
clopen bounded VF fiber has a same-base named uniform covariance radius.
The whole mixed partition is bounded before forgetting RV-tags. Inverse
continuity uses the checked closed-bounded Corollary 2.49. Restrictions use
a clopen inverse image under the continuous inverse; composition fixes its
intermediate tag on an open neighborhood in both directions. Results
6.8–6.9 retain `GammaPiecewiseRationalAffineInput`, genuine saturation above
aleph-zero, the original small real base, and nontrivial definable Gamma.
This is the existing author-accepted Section 2 background, not a new input.

Lemma 6.14 is implemented for the actual finite chains from Definition
6.11, including preliminary zero-centered preparation. The constructors
retain the original real base, nonzero finite branch tags, complete focus
graphs, continuous complementary-coordinate foci, named covariance radii,
and finite-aperture domination. Regularized RV-pullback loci descend to
existing RV tags by an original-base definable projection. The actual
centripetal graph fibers are the two clopen branches; triangular shears
have open images, and checked closed-bounded image theory makes those
images closed. The zero-centered map translates every selected coordinate
by the named nonzero center and retains every branch tag. Its coordinate
value is exactly the minimum of the original value and the center's value,
which proves double bounds. Its local derivative is the identity.

Finite chains are indexed by their actual changing RV arities and maps.
The generic-point induction uses genuine saturation, the original small
base and bijectivity to preserve VF independence through every prefix.
It yields a full total derivative of determinant one off an original-base
definable VF-small set, as approved in R102. Zero VF arity is proved at
every point. The characteristic-zero VF instance is derived from ACVF00.
The homeomorphism closure retains the existing accepted Gamma affine
background. The latest type/axiom audit passes 1179 declarations with only
`propext`, `Classical.choice`, and `Quot.sound`. This does not claim that
simultaneous preparation or all of Section 6 is complete.

There is no pending author decision after R102.

The initial preparation existence proof now chooses a uniform named mixed
radius, then a nonzero original-base VF point beyond it. A finite nonempty
definable subset of the punctured ball is obtained from the checked
elementary algebraic-closure model, and its unordered product is named over
the original base. The chosen radius is retained by the tagged translation.
Actual VF generation, field conventions, nontrivial valuation, genuine
saturation and smallness are explicit. The manuscript opening now explains
this attainable-radius choice. The full PDF remains pp.59–80; all 22 pages
were rendered and visually checked, and its right-panel request is queued.

Lemma 6.16 is also proved. The checked ordinary unary relation preparation
first prepares source membership, then the arbitrary VF/RV relation. The
restriction to the original unary source remains a special bijection and
has an RV-pullback image, including when some powerset values are empty.
The normalized and raw presentations have compiled same-base set and full
map-graph adapters. No ordinary preparation existence hypothesis is added.
The latest audit passes 1179 public declaration types and logical-axiom
reports. These ordinary exports seed the now-complete finite-aperture unary
construction. The higher-dimensional case of Proposition6.19 remains unfinished. FMT support separately proves its product
domain condition from invariance and proves continuity of freezing on a
clopen disc.

Lemmas6.22–6.23 now compile and are included in the 1179-declaration audit.
For6.22 the source is only required to have bounded VF projection and
doubly bounded RV projection. Its tubular Gamma extension is constructed
with a complete original-base graph; the tube retains the old RV tags and
bounds. The temporary radius representative appears only inside the proof
and is absent from the existential conclusion. Absolute Gamma values are
turned into a radius partition and bounded by the checked mixed2.53.

For6.23 the complete equality-of-values relation on two VF blocks is
definable over the original base. Open invariant level fibers make that
relation clopen. Its uniform mixed radius supplies one original-base named
local-constancy radius for the form, then6.22 bounds its values. The proof
requires only geometric invariance of the levels, a weaker hypothesis than
the paper's proper-invariant levels; the full form graph stays over S.
Neither proof assumes simultaneous preparation.


The 1179-declaration audit also includes actual RV-label projection and
RV grafting. The graft keeps every VF coordinate, is a proper covariant
homeomorphism, and has the identity total derivative everywhere. VF
coordinate projection preserves proper invariance, covariance, the old
tags, and the original radius names directly. These implement the
projection and grafting steps of the standard-contraction proof; they do
not yet prove existence of the full contraction list.

The finite-aperture unary foundations now include a common original-base
named coefficient for every finite definable family of nonzero foci.
Finite RV-indexed focus images and complete barycenter focus graphs are
proved, with a uniform bound for the root fibers. Every such actual unary
focus has a permitted centripetal realization with constructed covariance
data. Exact full-set formulas cover the core and noncore images. The
noncore root-count decrease is strict, including the singleton case,
because the finite cutoff excludes zero. The transported partition predicates are now handled by the checked
root-free-disc invariant described below; no preparation existence
assumption replaces that construction.


The actual unary root step and finite iteration are now in the
1179-declaration audit. Each step centers, retains its core flag, and
regularizes; only noncore roots are carried into the next original-base
definable root family. The construction terminates by strict decrease
and yields an actual special covariant chain. RV-pullback ambient sets
are preserved. The protected iteration chooses a common aperture for
any finite proper invariant family, and every literal restriction to
its own definable image remains a special covariant chain. Actual
centripetal core saturation is proved even when the source itself is
not yet an RV-pullback.

The root-free-disc invariant is now preserved through every protected
step. This establishes full simultaneous unary proper preparation; the
higher-dimensional induction in6.19 remains unfinished.


**Complete dimension cases: Proposition6.19 for n=0 and n=1.** A finite
original-base obstacle family controls all old RV tuples uniformly.
Root-free-disc control survives the actual protected finite-aperture
step: its noncore inverse is one translation on each output-label fiber,
and every protected core image is a full RV-disc. Strict root-count
induction therefore prepares every piece simultaneously. Original-base
zero-centered preparation and regularization remove preliminary source
conditions while preserving all restrictions. The actual VF-generated
field-base bridge is compiled. Arbitrary proper invariant unary sources
are handled against their RV-hulls. No higher-dimensional preparation
or new existence input is used. Zero VF arity is proved separately.

**Complete dimension case: Lemma6.27 for n=1.** The unary standard
contraction is an actual definable map to its own RV-image. Its lift is a
finite special covariant chain, hence a proper covariant homeomorphism
with total derivative and Jacobian one off an original-base VF-small
set. Every original RV tag is retained as a suffix through all changing
arities. The prepared target is recovered exactly from the contraction
labels and its recorded leading term. Higher-dimensional contraction
existence remains open in this checkout.

The audit passes1179 full declaration types and transitive axiom records,
using only propext, Classical.choice, and Quot.sound. The receipt and
scope explicitly distinguish these dimension cases from complete
numbered results and from completion of Section6.


The 1179-declaration audit additionally includes the finite-family FMT
construction. Complete hitting tuples give a finite original-base
definable hitting set. Averaging then constructs invariant center
functions and their full quotient open-ball graphs. Same-radius actual
open balls are proved disjoint or equal, and clopen in VF. Simultaneous
freezing has a full real graph over the original base, acts through actual
mixed maps, and composes with each actual focus map. Its product-domain
condition is proved from invariance of that current domain; continuity is
retained on every RV fiber. No individual ball representative or chosen
center is added to the base. This completes the finite-family freezing
operation, not the higher-dimensional preparation induction that must
select and glue its exceptional families.


**Complete numbered result: Lemma6.30, literal unary RV scope.**
The lift is an actual original-base definable finitary VF correspondence.
Each prescribed RV pair has exactly one output at every VF input and
contracts to exactly the original relation. Full VF-input finite hitting
tuples and definable means construct the center functions without naming
centers over arbitrary RV parameters. Genuine saturation supplies all
uniform finite bounds. Means preserve RV discs, including the zero fiber.
The full nondifferentiability locus of the actual unary mixed center map
has finite VF projection, uniformly over every output label. Its entire
RV-preimage is replaced by constant centers for the resulting finite
exceptional output family. Local constancy of nonzero input leading terms
preserves all good derivatives and gives zero derivative on the replacement
branches. Thus every branch is totally differentiable and continuous
everywhere, which strengthens the paper's partial differentiability claim.
Literal RV excludes its absorbing zero on the source, exactly as stipulated
in the manuscript. The actual VF-generated field-base adapter is compiled.
No abstract Gamma-generation or closure-smallness premise is used.

The 1179-declaration audit passes full types and transitive axiom checks
with only propext, Classical.choice and Quot.sound. Lemma6.30 is separate
from measured RV morphism lifting (6.31–6.33), which remains unfinished,
as do measured preparation, higher-dimensional preparation/contractions,
relative RV morphism factorization, and unary matching.


The 1179-declaration audit includes actual extension of a permitted
centripetal component from a whole old-label locus. An RV-pullback piece
of a regularized ambient set is proved to be such a locus; its literal
restriction is a special covariant chain, and the complementary VF map
is the identity with its retained branch tag. Finite compatible map
graphs glue over S. Components with disjoint active old-label loci glue
to permitted data when their coordinate and coefficient agree. A common
original-base named coefficient is constructed by an unordered product;
refining coefficients preserves permission and shrinks the actual core.
The old and new maps agree on the old noncore branch. Actual source
membership throughout the released annulus equals focus-graph membership.
These results implement component gluing and aperture geometry; the
lower-dimensional release construction and uniform chain selection in
higher-dimensional6.19 remain unfinished.

The post-FMT bound now has a checked adapter to Section2's
rv_indexed_gamma_family_bounded. Separately bounded Gamma rows over a
doubly bounded RV base admit one original-base named bound. Unit padding
handles empty rows. The complete Gamma-code union, supremum descent and
all original smallness/nontriviality/Gamma-affine hypotheses are retained.
No uniform bound on the original unfrozen VF-indexed data is assumed.


The original-base FMT continuity repair is now constructed, rather than
assumed. The actual scalar focus graph is extended by zero off its clopen
current domain. Proposition 2.55 bounds its canonical first-coordinate
discontinuity projection for each fixed RV tuple, and the checked finite
RV-to-VF image theorem makes the union finite over all existing labels.
The finite family of actual same-radius discs around this exception has
a complete original-base code pullback. Its existing finite exception set
is a definable hitting set, so the checked mean construction supplies
centers and their full quotient graph without a closure-smallness premise.
An attainable named radius makes every current-domain product condition
hold. The resulting actual FMT focus map is continuous on every RV fiber:
inside each frozen disc it is a continuous tail fiber; outside their
clopen finite union it agrees locally with the original map. The audit
passes 1179 full types and axiom records. Uniform chain selection and the
lower-dimensional release induction in 6.19 remain unfinished.


The 1179-declaration audit includes the actual projected focus graph and
its same-base descent through the coordinate projection. Continuity is
proved on that projected domain; every protected focus-graph piece is
proper invariant by 6.5, with the projected ambient bounds. A retained RV
label now specifies an actual carried-coordinate bundle, with full graph,
proper invariance, double bounds, taggedness, RV-pullback preservation and
an exact surjective projection. An individual permitted centripetal
component lifts to this bundle with its old focus, coefficient and
aperture-dominated radius unchanged. The new component leaves the carried
VF coordinate unchanged, and its full image is exactly the corresponding
bundle over the old component's image, with the retained tag shifted by
the new branch flag. This implements individual lower-dimensional release
components. Transport through all regularization/tag changes and the
complete finite release-chain induction remain unfinished.

The manuscript continuity paragraph is expanded using this independently
checked original-base repair. The updated 22-page PDF (manuscript 59–80)
was rendered and visually checked on all pages; no Section 6 overfull
lines were reported. The latest right-panel request returned queued.


Whole finite-chain transport after preliminary zero-centered preparation
is now proved in `CarriedFiniteChains.lean`. The chain syntax contains
only the original permitted centripetal operations, identity and actual
regularizations, and maps directly into `SpecialCovariantChain`. An
original-base carried refinement records all changing RV labels. Its
fibers are exactly old fibers or empty; this condition survives component
images, regularization and composition. Full regularization retains the
extra leading-term tag of the carried coordinate and checks its equality
with the retained old label. The entire regularized source is proved to
be the next actual bundle, not merely to have the same RV image. Both
primitive lifts and finite composition give literal special covariant
chains; the VF coordinate being carried is fixed at every point, and the
old map commutes exactly with selection of the retained labels. Prepared
old ambient targets give prepared carried targets. The audit passes1179
full types and axiom records. Applying this to all partition pieces,
constructing compatible literal restrictions, and the complete release/
fusion induction in higher-dimensional6.19 remain unfinished.


The latest 1179-declaration audit includes a single common carried finite
chain with compatible permitted component data on every protected piece.
Literal narrow restrictions compose to the restriction of that same map,
and exact full-set image identities give prepared partition images. The
actual unary root construction now returns this stronger certificate,
with no additional preparation premise. Consequently retained-RV cylinders
over unary sources admit simultaneous preparation fixing the extra VF
coordinate everywhere, including every regularization and branch tag.
This supersedes the earlier partition-compatibility limitation. Higher-
dimensional uniform family selection, identification of all released/core
branches and the complete release/fusion induction remain unfinished.


The 1179-declaration audit includes actual released-branch domains from the
old/new core tests, full-set annulus bundle equality, and proper, doubly
bounded, tagged projections. For compatible protected component data,
the actual narrow image is exactly the ambient annulus intersected with
its new full image, and factors through the same projection. Both the
actual ambient annulus and its projection are RV-pullbacks in every
dimension. `BinaryReleasedPreparation.lean` constructs simultaneous
preparation on the actual two-dimensional annulus using the unary root
algorithm and fixes the released coordinate everywhere. This supersedes
the earlier released-branch identification limitation. The new-core
replacement, uniform family selection and full release/fusion induction
remain unfinished; no full higher-dimensional 6.19 claim is made.


The 1179-declaration audit also covers the actual retained core selected
by its true output tag, full source witnesses, exact full-disc bundle
equality, proper/doubly bounded/tagged projections, and RV-pullback
ambient/projection geometry in every dimension. Compatible protected
core images equal the ambient core intersected with their new images
and factor through that projection. `BinaryCorePreparation.lean` gives
the actual simultaneous two-dimensional core replacement with its
core coordinate fixed. Both binary replacement branches are constructed;
higher-dimensional replacement, uniform family selection and complete
release/fusion remain unfinished.


The 1179-declaration audit includes complete original-base fixed-radius
focus congruence graphs and one named covariance radius uniform over all
RV labels. A lower valuation bound supplies a named common coefficient
for definable focus images even when infinite. Actual projected focuses
lift with full graphs and continuity to every protected source. The
constructor in `ContinuousFocusRealization.lean` produces a permitted
component in every positive VF arity, with one common coefficient and
compatible protected component data. `SimultaneousFocusSteps.lean`
includes actual regularization and one common finite-chain certificate.
These are supporting focus realizations; uniform complete preparation
data, higher-dimensional replacement and full release/fusion are pending.


The 1179-declaration audit retains all protected current-domain checks
through the actual continuity freezing. Freezing commutes with dropping
the target coordinate, leaves that coordinate fixed and preserves the
required focus leading term. A common named radius constructs finite
disc/center data and product certificates for the ambient and every
protected piece. `RepairedFocusSteps.lean` turns these repaired foci into
actual simultaneous permitted steps with regularization, assuming only
continuous remaining tail fibers; the unary projected-tail case is
unconditional. Complete preparation-data transport, uniform chain
selection and full release/fusion remain pending.


The 1179-declaration audit includes an exact original-base coordinate
bridge to the checked vertical-obstacle construction, retaining its
N+1 total bound. Finite unions control any finite predicate family.
Full mixed parameter graphs, actual finite root-mean maps, frozen root
fibers, bounds, partition control and equality with the repaired mean
are checked. Actual protected mean-root steps are constructed. General
permitted components and finite chains preserve RV-pullback ambients in
every VF arity; the noncore inverse and restricted-image formula are
exact. Actual remaining root fibers have a strictly decreasing uniform
bound, and protected coordinate-root control survives the step. Empty
roots give full coordinate bundles and an actual binary terminal
preparation from unary projected preparation. Selecting/preparing active
root loci while protecting arbitrary full-dimensional pieces, and the
complete termination/dimension induction, remain unfinished. These are
supporting constructions, not a full higher-dimensional 6.19 claim.


The 1179-declaration audit completes the n=2 case of Proposition 6.19.
`BinaryProperPreparation.lean` constructs a common actual special
covariant map and all literal protected restrictions, starting from an
arbitrary proper invariant RV-pullback; no preliminary double bounds,
root family, active-locus preparation or continuity hypothesis is supplied.
`BinaryFieldBase.lean` retains the manuscript's actual VF-generated field
base. The proof constructs the finite controlling roots, freezes their
actual indicator over the original base, prepares its proper unary
active locus while protecting arbitrary full-dimensional pieces, transports
roots and root control exactly, realizes the repaired actual mean,
strictly decreases the uniform bound, and iterates to the checked terminal
construction. All 1179 full public declaration types and transitive axiom
records pass, using only `propext`, `Classical.choice` and `Quot.sound`.
Preparation in VF arity at least three, higher-dimensional standard
contractions, measured preparation/lifting, RV morphism factorization and
unary matching remain unfinished. The original uniform release/fusion
induction is also not claimed as compiled. No complete Section 6 claim.


The 1227-declaration audit adds actual paired-disc geometry for unary
matching. Weak concentricity and continuity identify the target center
with its actual image and give arbitrarily small exact image discs. The
full paired-image formula, finite original-base radius families, named
finite-center separation, and canonical intersections construct disjoint
paired open cores with complete original-base graphs. The cores can be
chosen inside any prescribed definable neighborhoods of the finite center
family. These finite-center results concern a fixed scalar graph; they do
not by themselves prepare the whole mixed graph-fiber family.

`RVIndexedUpperRays.lean` and `RVIndexedEventualRadii.lean` separately prove
one original-base named cutoff for every nonempty definable Gamma upper
ray, or pointwise eventual Gamma property, over a doubly bounded nonzero
RV base. The proof bounds the positive bad-radius rows using the checked
Section 2 export; no definable choice of individual fiber cutoffs is a
premise. All 1227 full types and transitive axiom records pass with only
`propext`, `Classical.choice` and `Quot.sound`. The finite-aperture matching
construction, whole mixed graph-fiber adapter and measured adapter remain
unfinished, as do the higher-dimensional and measured results listed
above. No new numbered-result completion or complete Section 6 claim is
made by this support audit. Receipt:
`Section6/.scratch/audit-paired-cores-and-rv-thresholds.log`.


The 1241-declaration audit adds the centered-core volume calculation.
`CenteredPolydiscCharts` constructs the actual diagonal affine charts,
proves their exact projections and inverse formulas, and
`CenteredPolydiscDescent` derives volume comparison from the checked Gauss
graph construction. `CenteredDiscVolumeComparison` removes all chart-name
premises using a proved finite auxiliary real extension, retaining the
original definable VF-small exception. `CenteredGammaVolume` and
`PairedCoreRadiusIdentity` give the exact radius and volume-form identities
in the actual Gamma quotient, including arbitrary unnamed radii.
`OpenGraphRestrictions` carries VF charts, full derivatives and Jacobians
through literal restrictions to open VF fibers; `RestrictedCoreVolume`
constructs the restricted-image bijection and proves its volume identity
from the ambient map's Jacobian condition. Thus this local core calculation
requires neither an extra volume theorem nor a generic-derivative input.

All 1241 full public types and transitive axiom records pass with only
`propext`, `Classical.choice` and `Quot.sound`; the pins are unchanged.
Receipt: `Section6/.scratch/audit-centered-core-volume.log`.
The finite-aperture matching and its whole mixed graph-fiber/global
RV-matching adapters remain unfinished. In particular the constructed
paired open radii have not yet been realized by the permitted global
aperture coefficients; that requirement is not inferred from the local
radius identity. The higher-dimensional and measured results listed
above remain in progress. No additional complete numbered result is
claimed by this support audit.


The 1274-declaration audit completes the RV and measured adapters for an
actually prepared unary whole-disc matching. `RVTagMatching` constructs
the actual definable quotient map, proves its commuting square and
bijectivity, and retains doubly bounded supports. `RVContractedGammaForms`
constructs the descended forms with full original-base raw Gamma graphs
and exact value images. `UnaryTagDiscFibres` identifies each nonempty
old-tag fiber with its full centered RV disc. `NamedTagFibres` supplies
actual definable fixed-tag source domains and their exact full images.
`WholeDiscMeasuredMatching` restricts the actual ambient map to these
domains, retains the original VF-small Jacobian exception through a
proved finite parameter extension, and proves the radius identity at
every label. `PreparedUnaryRVMatching` packages the actual RV bijection,
both full form graphs, bounded supports and the complete volume identity.
The source forms, target forms and their label constancy, and an actual
whole-disc matching are explicit hypotheses; the preparatory special
bijections are not supplied as a completed theorem.

`AttainableRVThresholds` also replaces a uniform eventual Gamma cutoff by
one actual original-base named nonzero VF point, with its entire larger
radius tail satisfying the condition. All 1274 complete types and
transitive axiom records pass with only `propext`, `Classical.choice` and
`Quot.sound`; the pins remain unchanged. Receipt:
`Section6/.scratch/audit-prepared-unary-rv-matching.log`.
The finite-aperture construction of the whole mixed graph-fiber matching
remains unfinished, including realization by the permitted coefficient
choices. Thus the full existence statement 6.38 is not claimed. Preparation
in arity at least three, higher standard contractions, measured preparation
and lifting, and RV morphism factorization also remain unfinished.


The 1332-declaration audit completes the unary measured preparation
construction. `UnaryMeasuredPreparation` starts from an arbitrary proper
source and constructs one actual special covariant map, its doubly bounded
tagged RV-pullback target, an actual transported Gamma map constant on
all target RV labels, and every literal protected finite-family
restriction. `UnaryMeasuredPartitionPreparation` derives ambient
properness and open global Gamma levels from the actual finite proper
cover hypotheses of 6.21. `UnaryMeasuredFieldBase` retains the actual
VF-generated field convention. `UnaryMeasuredContraction` constructs the
surjective actual RV contraction, its full descended Gamma graph and the
exact original-form factorization; the target form is proved equal to
the original form composed with the actual inverse.

The proof constructs the original-structure Gamma presentation and full
mixed-code/Map bridges, transports open levels through retained-label
inverses, and chooses one named radius protecting all levels, including
ambient membership. One original-base finite obstacle set controls the
entire Gamma form and the finite pieces. True-core constancy and exact
noncore inverse translations preserve this form control through each
strict root-count decrease. The complete terminating root induction and
preliminary preparation are constructed without a root, coefficient,
form-transport or preparation premise. Individual Gamma levels are never
assumed S-definable and are not enumerated.

All 1332 complete public types and transitive axiom records pass with only
`propext`, `Classical.choice` and `Quot.sound`; the pins are unchanged.
Receipt: `Section6/.scratch/audit-unary-measured-preparation.log`.
The additional category-valued lifting clause of 6.21 and its VF arity
at least two cases remain unfinished; no full 6.21 claim is made. The
higher-dimensional preparation/contraction, measured morphism lifting,
RV factorization and finite-aperture existence construction of unary
matching also remain open. The prepared matching adapters through the
1274-declaration audit remain valid, with their preparation hypotheses
explicit.


The 1358-declaration audit completes the unary preparation and degree-one
finite-RV-fiber lifting case of 6.21. `lemma_6_21_unary` constructs one
common actual special preparation under the finite proper cover/level
hypotheses. For each selected piece with finite RV fibers it constructs
an actual finite-volume, doubly bounded RV object and a definable Gamma
form, together with the literal special map of that piece into its exact
lift. The lift maps retain the ambient preparation's point formulas and
RV arity. `lemma_6_21_unary_vfGenerated` retains the actual VF-generated
field convention. The source need not already be a pullback, so the
construction also covers the manuscript's proper-source extension.

`FiniteRVFiberTransport` supplies fiber finiteness from the checked
companion dimension theorem, with its RV exchange input constructed by
the checked earlier-result export. `PureRVDiscQuotients` and
`PreparedRVObjects` construct the actual pure-RV domain, finite volume
map, double bounds and exact full lifted set.
`MeasuredRVLiftData.measure_identity_ae` combines exact form preservation
with the approved definable VF-small unit-Jacobian exception.
`UnaryMeasuredPieceLifts` requires finite RV fibers only of the selected
piece, preserving the R170 distinction; no ambient finiteness premise is
introduced. All 1358 complete types and transitive axiom records pass with
only `propext`, `Classical.choice` and `Quot.sound`. Pins are unchanged.
Receipt: `Section6/.scratch/audit-unary-measured-lifting.log`.

This supersedes the earlier pending unary category-clause note. No full
higher-dimensional 6.21 claim is made: its arity at least two cases and
further head-start/degree adapters remain unfinished. Higher preparation
and contractions, RV factorization, measured RV-morphism lifting and the
finite-aperture existence construction for unary matching also remain
unfinished. No complete Section 6 claim.

The 1366-declaration audit adds the zero-VF-arity, degree-zero case of
6.21. Its common map is the identity, each finite-RV-fiber piece has an
actual degree-zero measured RV object and lift, and the measure identity
holds everywhere with empty determinant one. Prepared measured lifts now
also have an arbitrary-arity adapter, conditional on an actual tagged
RV-pullback and an RV-label-constant Gamma form. This adapter does not
supply higher-dimensional measured preparation. The audit allows only
`propext`, `Classical.choice`, and `Quot.sound`.

The 1423-declaration audit completes binary measured preparation and
the degree-two selected-piece lifting clause of 6.21. The actual common
coordinate roots control every Gamma level over the original base.
Measured continuity repair, active-root preparation, strict root decrease
and the complete binary iteration are constructed; empty roots give
actual Gamma descent to the unary base and a carried permitted terminal
preparation. No supplied preparation certificate or individually named
Gamma level is assumed.

`binary_measured_preparation` applies to any proper source, and
`binary_measured_partition_preparation` derives its ambient hypotheses
from the actual finite proper cover. `lemma_6_21_binary` returns one common
map and actual degree-two measured RV lifts on each selected finite-RV-fiber
piece, with the same point map and RV arity. It does not assume finite RV
fibers of the whole ambient. `lemma_6_21_binary_vfGenerated` keeps the
actual field-base convention. The approved AE Jacobian/measure identity
applies to these lifts. General positive-arity adapters retain prepared
form descent and literal selected-piece restrictions. All 1423 full types
and transitive axiom records pass with only `propext`, `Classical.choice`
and `Quot.sound`; the dependency pins are unchanged.

The numbered 6.21 coverage is now zero-arity/degree-zero, unary/rank-one
and binary/rank-two. VF arity at least three and further degree/head-start
adapters remain unfinished. This does not assert binary standard
contractions, RV morphism factorization or measured RV-morphism lifting,
or solve the finite-aperture unary matching construction.

The 1484-declaration audit adds the complete degree-one case of 6.29,
including actual measured RV isomorphisms and full finite-volume and
doubly bounded intermediate-chain conditions. It also adds a generic
measured RV lift in every positive degree over the actual VF-generated
field base: the full derivative and the prescribed Gamma determinant
identity hold off one original-base definable VF-small exception.

The temporary definable closure is proved small using the checked
`IntegrationInACVF.Section6.closureBase_real_small` export. Its real
parameters are individually definable over S and eliminated from the
complete map and exception graphs; checked VF-dimension invariance
retains the strict dimension bound over S. The weighted lift uses the
checked `SpecialTransformations.Section9.exists_weighted_liftMap_of_rvIso`
export with all closure-generation, characteristic, nonzero-volume and
saturation hypotheses supplied. No HK assumption is added. The original
parameter base is not assumed definably closed.

This is almost-everywhere measured RV-morphism lifting, not the everywhere
conclusion of 6.31 and not the continuous relatively unary factorization
of 6.33. The latter, factorization in RV degree at least two, the higher
preparation/contraction cases and the actual finite-aperture unary matching
construction remain unfinished. All 1484 complete public declaration
types and transitive axiom records pass with only `propext`,
`Classical.choice`, and `Quot.sound`; all exact dependency pins remain
unchanged.


## Unary everywhere measured lifting — audited at 1533 declarations

The unary exceptional set is finite inside the actual finite-volume RV
lift, and its entire original-label image is finite. Original-base finite
RV center maps construct affine replacement lifts on those whole discs.
Their actual inverses, total derivatives at every point and exact Gamma
measure identity are checked. Literal measured restrictions and finite
graph gluing retain the generic lift on the other labels, giving an
everywhere differentiable, graph-fiber-continuous unary measured lift over
the actual VF-generated field base. No individual RV label or VF center
is added as a parameter.

Nonzero RV lifts have full clopen polydisc fibers in every degree. Actual
double bounds give proper invariance by the proved original-base clopen
criterion. Fixed-label graph ranges of a bijective lift are entire target
RV polydiscs. Together with the total charts and the checked covariance
and inverse-continuity theorems, this constructs a relatively unary proper
covariant homeomorphism in degree one (the doubly bounded degree-one case
of 6.33). Degree-zero measured RV isomorphisms also have actual lifts with
the empty determinant identity everywhere.

All 1533 complete public declaration types and transitive axiom records
pass with only `propext`, `Classical.choice` and `Quot.sound`; exact pins
are unchanged. Everywhere measured lifting and relatively unary
factorization in degree at least two remain unfinished, as do the higher
preparation/contraction cases and actual finite-aperture unary matching.
The manuscript and revised PDF are unchanged in this proof-only update.


## Every-degree finite-label lifting — audited at 1575 declarations

The full degree-one unmeasured Jacobian lifting statement (6.31) is now
constructed from actual Gamma volume maps and a proved structural measured
balance, with full total derivatives everywhere and graph-fiber
continuity. The unmeasured degree-zero case is also checked.

Finite original RV label objects in every degree now have actual
original-base coordinate and tuple VF center maps. These construct
literal diagonal affine lifts; the reverse center families give the exact
inverse. A full fixed-label polydisc chart proves total differentiability
everywhere, with determinant equal to the product of the center ratios.
The original measured RV balance proves the exact Gamma measure identity.
The VF-generated field-base adapters and the doubly bounded proper
covariant homeomorphism conclusion are constructed. Unmeasured finite-label
Jacobian lifting follows from constructed structural Gamma forms.
This completes the RV-dimension-zero base of everywhere measured lifting,
but does not yet construct the required relatively unary factorization in
higher degree. Positive-RV-dimension lifting in degrees at least two,
higher proper preparation and contractions, and the actual finite-aperture
unary matching construction remain unfinished.

The audit passes all 1575 complete public declaration types and transitive
axiom records with only `propext`, `Classical.choice` and `Quot.sound`.
Exact dependency pins and the manuscript/PDF are unchanged.


## Finite-label unary factorizations and VF chains — audited at 1625 declarations

The RV-dimension-zero case of 6.29 is now constructed in every positive
degree, in all four unmeasured/measured and bounded/unbounded variants.
Actual coordinate-replacement maps retain the original label domain;
every intermediate object has finite volume. The intermediate Gamma forms
keep the original total weight exactly, and double bounds are certified
at every step of the bounded chains.

For each relatively unary RV component, the target center family uses
the identical source VF center in every unchanged coordinate. Its actual
affine lift therefore fixes those VF coordinates exactly. Full total
charts and Gamma measure identities compose everywhere in the checked
`EverywhereMeasuredRVLift` record. Every finite-label measured RV chain
has a constructed actual relatively unary VF lift chain. This completes
the finite-label case of 6.33 in every positive degree over the actual
VF-generated field base; with double bounds every component and the full
composite are proper covariant homeomorphisms. The degree-zero direct
lifting statements remain separately checked.

All 1625 full public declaration types and transitive axiom records pass
with only `propext`, `Classical.choice` and `Quot.sound`. Dependency pins
and the manuscript/PDF are unchanged. Positive-RV-dimension factorization
and everywhere lifting in degree at least two, the higher proper
preparation/contraction cases, and actual finite-aperture unary matching
remain unfinished.


## Uniform original-base RV inverse obstacles — audited at 1634 declarations

A new compactness construction covers every parameter tuple by either a
finite inverse-row bound or a finite algebraic relation. Its finite
subcover gives one original-base finite-fibre exceptional relation and
one bound for every complementary inverse row. The checked scalar RV
finite-exception theorem supplies the required alternatives at each
actual enlarged small tuple base; the construction then removes those
temporary parameter names from the entire family. Arbitrary finite real
parameter tuples are retained. This supplies the uniform-exception step
needed for positive-RV-dimension factorization without an assumed
elimination-of-infinity statement.

Actual definable label bijections between nonzero finite-volume RV
objects now also have constructed category isomorphisms, with both
finite-volume-image conditions proved from the given volume fibres.
All 1634 complete public declaration types and transitive axiom records
pass with the three standard logical principles; exact pins and the
manuscript/PDF are unchanged. The positive-dimension factorization,
higher preparation/contraction and finite-aperture matching work continues.


## Actual measured good coordinate pivots — audited at 1661 declarations

Full real-code image graphs now define the unary volume-coordinate
correspondences of actual RV morphisms. Their finite forward fibres
supply every hypothesis of the uniform inverse-obstacle theorem. The
actual good original-label domains and last-coordinate replacement maps
are constructed. Their volume fibres are proved finite from finitely many
possible old volume values and the original finite-volume hypothesis.
Thus every good pivot is an actual relatively unary RV isomorphism,
with no assumed finiteness condition on the new volume.

The intermediate Gamma forms keep the original total weight exactly.
The full original label domain and every replacement volume coordinate
retain double bounds. These constructions supply the good-pivot part of
the positive-RV-dimension induction; residual dimension drop and the
complete induction remain unfinished.

The audit passes all 1661 complete public declaration types and transitive
axiom records with only the three standard logical principles. Exact
pins and the manuscript/PDF are unchanged.


## Residual RV dimension drop — audited at 1669 declarations

The residual original-label domain is now the actual definable complement
of the finite union of all good pivot domains. On each fixed old source
prefix, all target volume coordinates lie in the corresponding finite
obstacle rows. Their finite product gives finitely many target volume
values; target finite volume and injectivity of the actual label map
then prove that the old source-prefix map is finite-to-one on the entire
residual domain. Consequently its RV dimension is strictly below the
positive ambient degree. This is a proved map and dimension inequality,
not an assumed induction input.

All 1669 complete public declaration types and transitive axiom records
pass with the three standard logical principles. Exact pins and the
manuscript/PDF remain unchanged. The retained-coordinate induction and
global finite-piece factor assembly of 6.29 remain unfinished, as do the
higher preparation/contraction and finite-aperture matching cases.


## Coordinate paths and actual volume changes — audited at 1752 declarations

Actual original-base RV scalar multiplication and division maps now give
one-coordinate category isomorphisms with finite volume and explicit
double bounds. Three arithmetic steps realize a coordinate transposition.
Constructed Gamma forms retain total weight, and every structural
coordinate permutation in positive degree has a measured relatively unary
factorization with bounds at every intermediate object. A definable
piecewise map replacement extends an individual relatively unary volume
change by the old volume on the complementary labels.

The checked earlier RV exchange theorem supplies genuine algebraic
closure. A minimal finite support proves one-coordinate exchange for a
possibly dependent generating tuple, including the separate rank-zero
case. Induction with one retained coordinate gives finite indexed paths
between any two interalgebraic volume tuples. Actual finite-volume RV
isomorphisms meet that hypothesis through their actual volume-pair finite
projection. Original-base finite-relation loci then certify actual finite
fibres for selected volume maps, without choosing new parameters.

All 1752 complete public declaration types and transitive axiom records
pass with only `propext`, `Classical.choice`, and `Quot.sound`. Exact pins
and the approved manuscript/PDF remain unchanged. Finite-piece cover
extraction and global assembly for general positive-dimensional 6.29 are
still being implemented. No additional complete numbered theorem is
claimed at this milestone; the higher preparation, contraction, lifting
and matching cases remain unfinished.


## Actual factorizations on a finite cover — audited at 1799 declarations

Genuine saturation extracts finitely many original-base definable route
pieces covering every label of an arbitrary finite-volume RV
isomorphism. Each visited volume has a complete finite-relation
certificate on its piece. The actual intermediate RV objects are nonzero
and finite-volume, and all selected coordinates inherit the endpoint
double bounds.

Each certified route now compiles into an actual measured relatively
unary category chain. Constructed intermediate Gamma forms retain the
original total weight. The explicit source and target identifications
recover the literal restricted original isomorphism, including its
prescribed label map. Thus every positive-degree measured RV isomorphism
has actual factorizations on a finite original-base definable cover,
with double bounds at every intermediate object when the endpoints are
bounded. Global assembly into one whole-domain chain remains unfinished.

All 1799 complete public declaration types and transitive axiom records
pass with only the three standard logical principles. Exact dependency
pins and the approved manuscript/PDF remain unchanged. This is supporting
coverage for general 6.29; no new complete numbered result is claimed
until the whole-domain assembly is compiled. Higher preparation,
contraction, everywhere lifting and matching remain unfinished.


## Lemma 6.29 in every positive degree — audited at 1829 declarations

All four variants of Lemma 6.29 now have actual whole-domain relatively
unary category factorizations in every positive degree and arbitrary RV
dimension. The composed label map is exactly the prescribed original
morphism. Every intermediate object has actual finite volume; measured
Gamma forms are explicitly constructed, and every intermediate object
retains double bounds in the bounded variants.

The proof uses genuine earlier RV algebraic exchange, minimal finite
supports, and finite indexed coordinate routes. Original-base finite
algebraic relations and genuine saturation supply a finite route cover.
Each local route compiles to a measured chain. Its components extend
along definable injections to the whole old label domain while retaining
the old volume elsewhere. Finite assembly changes only previously
unprocessed labels. Canonical intermediate forms retain the original
total weight throughout, and endpoint identifications recover the exact
morphism. Constructed structural measured forms and forgetting then give
the unmeasured variants. No HK result is used as an assumed input.

The positive-degree hypothesis is explicit: the relatively unary
coordinate definition has no index in degree zero. Existing direct
zero-degree lifting results remain separate. This does not add a new
manuscript convention or claim a degree-zero unary factorization.

All 1829 complete public declaration types and transitive axiom records
pass with only `propext`, `Classical.choice`, and `Quot.sound`. Dependency
pins and the approved manuscript/PDF remain unchanged. Higher-arity
proper preparation, higher standard contractions, positive-RV-dimension
everywhere/relatively unary lifting in degree at least two, and the
finite-aperture unary matching construction remain unfinished.


## Whole bad-label dimension drop and repair — audited at 1846 declarations

The actual RV-boundary theorem now has every former geometric premise
supplied by checked earlier-result adapters. Its original-base boundary
has an actual finite-to-one map to one fewer RV coordinate. Erasing all
RV labels from a VF-small set preserves its dimension bound, proving
that its entire VF projection misses a point in every nonzero RV
polydisc.

For an actual nonzero finite-volume RV lift, all old labels touched by
a VF-small exception map finitely into that boundary. Their RV dimension
is therefore strictly below the ambient positive degree. Full total
measured derivatives now glue across whole label pieces in every degree.
Combining the original-field-base almost-everywhere lift, this dimension
drop and the actual repair proves the full-degree lifting induction step
under an explicit smaller-label-lift induction hypothesis. That
hypothesis is not claimed as discharged: the lower-dimensional head/tail
constructions and relatively unary higher-degree VF lifting remain
unfinished.

All 1846 complete public declaration types and transitive axiom records
pass with only the three standard logical principles. The complete
positive-degree 6.29 result remains audited. Exact pins and the approved
manuscript/PDF are unchanged.


## Finite heads and full coefficient derivatives — audited at 1875 declarations

Finite families of scalar and tuple coefficient maps now have full total
VF derivatives outside one original-base set of whole old labels of RV
dimension below the positive source degree. Rectangular output charts
include the empty tuple case. Finite coordinate heads have constructed
Gamma forms retaining the original total weight and old labels, with
actual simultaneous source/target finite-head covers. Structural
coordinate permutations have actual everywhere differentiable measured
VF lifts with determinant Gamma value one. These are supporting results
for the lower-dimensional lifting induction; they do not yet discharge
that induction or the higher-degree relatively unary VF chain theorem.

All 1875 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur.


## Full affine finite-head lifting step — audited at 1913 declarations

The affine tail now has actual same-base slope maps and a full total VF
derivative that includes every head-dependent coefficient. Actual
finite-head lifts extend to bijections on the complete original fibres;
full derivatives and the prescribed determinant hold away from one
whole-label set of RV dimension strictly below the positive head degree.
The tail centres, correction scalar and determinant map are constructed
over the original VF-generated field base, with complete graph descent.
The measured finite-head step repairs that entire bad-label domain using
an explicit smaller-rank induction lift. Restriction, disjoint gluing and
finite-cover gluing preserve the full measured identity everywhere.

All 1913 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. The final
rank induction and higher-degree relatively unary VF chain construction
are still separate obligations.


## Every-degree everywhere RV lifting — audited at 1925 declarations

The strong induction on the actual RV dimension of the old label domain
is complete. The finite-label base, full-degree generic repair and the
selected finite-head construction in positive codimension now discharge
all smaller-rank lift premises. `lemma_6_31_measured_vfGenerated` and
`lemma_6_31_vfGenerated` construct actual original-base lifts in every
degree and arbitrary RV dimension, with full total VF derivatives and the
exact Gamma Jacobian identity at every point. Fibre continuity follows.
Doubly bounded measured endpoints have actual proper covariant
homeomorphism lifts. The actual VF-generated field, nontrivial valuation
on that field, standing definable Gamma assumption, genuine saturation
and smallness are explicit, as in the preceding unary/finite-label
adapters. No HK input or smaller-rank lifting premise remains.

All 1925 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. The
higher-degree relatively unary VF chain assertion of 6.33, preparation
in arity at least three, higher standard contractions and unary matching
remain unfinished.


## Relative weighted local polynomial lifts — audited at 1952 declarations

Finite-to-finite relatively unary RV correspondences over a genuinely
generated base now have constructed weighted polynomial fibre bijections
that fix every inactive VF coordinate exactly. Finite RV rows supply the
active-coordinate algebraicity. Inactive equations are literal diagonals;
a local strengthening of the checked weighted construction retains its
integer row formula. Actual diagonal RV-fibre anchors and nonzero partial
Jacobian rows force distinct integer coefficients. Residue characteristic
zero makes the row multiplier nonzero on the full prescribed fibre, so
its diagonal factor vanishes. Complete real graphs are definable over the
coefficient-name base, and restriction to the inactive diagonal retains
both unique-existence clauses. This is local lifting, not yet the global
relative measured VF chain assertion of 6.33.

All 1952 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur.


## Original-base relative measured lifts almost everywhere — audited at 1960 declarations

Relative weighted good domains and global gluing are constructed from the
actual local polynomial graphs. Every RV pair uses a polynomial graph
with the exact inactive VF diagonal and weighted Jacobian blocks. The
resulting definable bijection fixes every inactive VF coordinate at every
point and has the structural weighted Jacobian at independent VF points.
Complete real-graph parameter descent and the checked generic derivative
exception theorem give a relatively unary measured lift over the actual
original VF-generated field base, with full total derivatives and the
exact Gamma measure identity off one original-base VF-small set. The
whole old-label image dimension drop is already available separately.

All 1960 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. Extending
relative VF chains to the full old label domain, smaller-rank chain repair
and the full 6.33 assembly are still unfinished.


## Whole-label extensions of actual VF chains — audited at 1999 declarations

Local measured VF lifts and entire relatively unary VF chains now extend
to a fixed global old-label domain by the identity off the chosen piece.
The construction retains bijectivity, the full total derivative and exact
Gamma identity everywhere, the active VF coordinate, finite volume and
every intermediate double bound. The initial volume-preserving identity
lift identifies the chain with its literal global source. This supplies
the chain-extension step needed for exceptional-label repair in 6.33.

All 1999 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. Smaller-rank
chain repair and the full 6.33 assembly remain unfinished.


## Exceptional-label VF chain repair — audited at 2009 declarations

A chosen relatively unary lift now restricts to any whole-label good
domain with its full derivative, measure and exact inactive coordinates.
Finite gluing retains the same inactive diagonal. An actual VF chain on
the exceptional label domain extends globally; a final relatively unary
map is the identity there and the original lift on the complement. The
composite has the prescribed original RV map and all intermediate double
bounds. The full-degree chain step combines the original-base relative
almost-everywhere lift, the proved RV-boundary dimension drop and 6.29.
Its strictly smaller RV-rank chain premise remains explicit until the
positive-codimension construction discharges the rank induction. The
finite-label base now also retains actual intermediate bounds.

All 2009 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. Full 6.33
remains unfinished; the conditional full-degree step is not claimed as
the completed numbered theorem.


## Actual measured VF permutation chains — audited at 2047 declarations

Full reciprocal differentiation is proved directly in the actual value
quotient for arbitrary valuation rank. Actual definable VF multiplication
and division maps have explicit inverses on entire RV polydiscs. Their
full determinants are computed from literal identity inactive rows and
the active scalar derivative; the values match the constructed Gamma
forms everywhere. Coordinate transpositions and arbitrary permutations
therefore have actual relatively unary measured VF chains, including
inverse permutations and every intermediate double bound. This supplies
the coordinate-change part of the positive-codimension 6.33 construction.

All 2047 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. Padding,
smaller-head VF chain extension and the full rank induction remain open.


## Full positive-degree measured VF chain lifting 6.33 — audited at 2113 declarations

Strong induction on the actual RV dimension of the original label domain
now discharges every smaller-rank VF chain premise. The finite-label
base retains actual intermediate double bounds. In full degree, the
original-base relatively unary almost-everywhere lift is repaired on
whole exceptional label fibres of strictly smaller RV rank. In positive
codimension, actual triangular chains replace tails by unit RV pads in
both directions, carry the constructed full-degree head chain with its
entire padded VF tail fixed, and return the selected coordinates through
actual VF permutation chains. Every replacement retains finite volume
through its unchanged finite head; forms retain the original total weight.
Finite original-base covers assemble into one whole-domain actual chain.

Thus `lemma_6_33_vfGenerated` constructs actual relatively unary measured
VF chains in every positive degree and arbitrary RV dimension, with the
exact original RV map, full total derivatives and exact Gamma measure
everywhere, and every intermediate double bound. The doubly bounded
variant proves proper covariant homeomorphisms for every component and
the complete composite. The actual VF-generated field base, nontrivial
base-field valuation, standing definable Gamma assumption, smallness and
genuine saturation remain explicit, as for the full 6.31 construction.
The proper-homeomorphism clause retains the accepted Section 2 Gamma
piecewise-rational-affine background. Degree zero remains separate from
chains indexed by a positive VF coordinate.

All 2113 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. No HK
lifting theorem or smaller-rank chain existence is an assumed input.
The active next target is the general higher-dimensional 6.19 induction.
The cases with zero, one and two VF coordinates are complete; higher
preparation, higher standard contractions and unary matching remain open.


## General aperture-branch preparation transport — audited at 2128 declarations

The actual simultaneous centripetal certificate now survives carried
identity, regularization, centripetal steps, composition and exact
source/target/partition transport. Consequently a prepared projected
family lifts to full cylinders in every dimension while retaining its
common permitted component sequence and fixing the released coordinate
at every point; the result can itself be carried in the next dimension.
The root-free terminal step is proved from an actual projected chain.
Concrete preparation witnesses for the projected family lift to both
the retained core and the released annulus using the exact full-set
factorization of the ambient and every protected original piece.

All 2128 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. These
results implement the geometric branch transport in the 6.19 induction.
They retain an explicit actual projected preparation premise; the
general existence induction, uniform fibrewise construction and fusion
are still unfinished. Full 6.19 remains proved only through VF arity two.


## Complete unbounded unary RV-data preparation — audited at 2167 declarations

A unary base preparation now has an actual simultaneous lift in arbitrary
ambient VF arity. Its coefficient protects every proper full piece, its
common component certificate composes on literal images, every inactive
VF coordinate stays fixed, and all source RV labels are retained.
Each unary step is an exact translation on a fixed target-label fibre,
so its inverse preserves VF differences and the same radius controls an
arbitrary complete data value through every strict root decrease.

For an arbitrary original-base definable relation in one VF coordinate
and any number of RV coordinates, including unbounded RV output, the
actual common finite obstacle set and exceptional discs are constructed.
Freezing has complete original-base centre graphs and checks the current
ambient and every protected piece's product condition. The complete
powerset-valued rows then admit actual unary special preparation together
with the ambient lift. No initial uniform row bound is assumed.

All 2167 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. This
completes the unary data-preparation part needed for the general 6.19
argument. Uniform selection of the fibrewise chains and the final fusion
induction remain unfinished; full 6.19 is still proved only through VF
arity two. Work remains focused on that general induction.


## Definable continuous focus templates — audited at 2192 declarations

Complete continuous VF graph rows defined over a real parameter tuple
now promote to actual original-base graph templates. Totality,
single-valuedness, continuity on the entire VF domain and pointwise
constraint satisfaction have proved first-order definable admissibility
loci. Genuine saturation extracts a finite original-base template family
covering a definable parameter domain. Each admissible row has its
actual continuous function and exact complete graph. Proper partial
focus maps enter through checked continuous total zero extensions,
retaining precisely the existing RV labels in their parameter base.

All 2192 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. These
are ingredients of the uniform-choice step for 6.19. The serialization
and uniform selection of complete component sequences, followed by the
release/fusion induction, remain unfinished. Full 6.19 is still proved
only through VF arity two.


## Synchronized covariance and complete focus graphs — audited at 2259 declarations

The actual common coefficient and full focus graph now reconstruct a
permitted ambient component and every compatible protected restriction.
Canonical tagged active radii and one original-base named complementary
radius work simultaneously for the ambient and all protected pieces.
The active-coordinate independence condition is a proved first-order
parameter condition, with an exact characterization for actual maps.
Finite operational shapes and type-valued realizations retain all
intermediate RV arities. Unary data preparation now retains the stronger
focus/coefficient compatibility certificate. That certificate survives
whole carried chains and exact retained-core/released-annulus transport,
including every protected piece and the carried VF coordinate.

All 2259 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. These
results strengthen the general 6.19 construction; they do not establish
its missing uniform choice of whole component sequences or the final
release/fusion induction. Full 6.19 is still complete only in VF arities
zero, one and two. No author decision is pending.


## Pointwise admissibility and whole RV-family templates — audited at 2343 declarations

The canonical active aperture is now recovered from the actual complete
focus graph on each inhabited old-label fibre, with value one on empty
fibres. Its complete Gamma name uses exactly the old labels. No designated
coordinate storing the active leading term is required. Every actual
synchronized component on an RV-pullback ambient has a finite-metadata
pointwise covariance form preserving the original component map and all
protected restrictions. Complete focus data reconstruct the permitted
component from that form.

Independence of the active coordinate, correct leading terms, source
invariance and erased-coordinate covariance now have proved first-order
parameter loci with exact actual-map interpretations. A whole RV-indexed
continuous VF family has one definable admissibility condition quantifying
all its old labels. Whole family graphs promote to original-base templates,
and genuine compactness constructs finite template covers. Proper partial
focus maps supply complete continuous total extensions as whole-family
graphs. Admissible templates retain complete original-base family graphs
and reconstruct actual definable maps and full partial focus data. Named
Gamma values likewise have definable template admissibility, complete
value names, promotion and finite covers, without adjoining a chosen
real representative.

All 2343 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. Whole
component-sequence serialization and its uniform selection, then the
release/fusion induction, remain unfinished. Full 6.19 is still complete
only through VF arity two. Work remains focused on its general induction;
no author decision is pending.


## Complete component admissibility, promotion and finite covers — audited at 2402 declarations

Current mixed domains and active RV loci now have complete original-base
parameter templates. Relational transition images specialize to the
literal images of the actual restricted maps. Tagged-source geometry
and terminal RV-pullback preparation have proved first-order parameter
conditions and exact actual-set interpretations in every arity.

A complete component template contains the actual coordinate, active
locus, whole continuous RV-indexed focus family, named VF coefficient
and named Gamma radius. One definable admissibility locus checks its
complete geometry and every protected source condition. Admissibility
reconstructs an actual permitted component and aperture-compatible
components on every protected piece. Every actual synchronized component
on a pullback fibre promotes to an admissible original-base template,
retaining its exact coordinate, locus, coefficient and whole focus family.
Reconstruction agrees with the original component on its entire source,
including its core test and branch map. Genuine compactness now supplies
finite covers by these complete component templates. Smallness after
adding the real parameter tuple and nontrivial definable Gamma are derived
from the original hypotheses.

All 2402 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. Uniform
selection of whole finite component sequences and the subsequent
release/fusion induction remain unfinished. Full 6.19 is still complete
only through VF arity two. The next step is the exact first-order coding
of transitions and their finite compositions. No author decision is pending.


## Whole finite preparation programs — audited at 2471 declarations

Identity, regularization and centripetal transitions now have complete
original-base first-order graphs, including inactive foci and both
aperture branches. Quantified composition computes the exact composite
and every intermediate ambient and protected image. Whole finite
programs have definable admissibility and terminal preparation tests.
Admissibility reconstructs a synchronized permitted chain; conversely,
every actual synchronized chain on a pullback fibre promotes with its
exact composite graph. Prepared programs reconstruct complete actual
synchronized preparation witnesses.

Genuine compactness now gives finitely many complete prepared programs
for a definable family of locally prepared fibres, with common finite
bounds on length and output RV arity. Their formula-choice cover has a
same-base definable disjoint refinement. Parameter-extension smallness
and nontrivial definable Gamma are derived from the original hypotheses.

All 2471 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. This
finishes the whole-sequence coding and uniform finite-choice step.
The global release/fusion induction remains unfinished; full 6.19 is
still complete only through VF arity two. Work continues with compatible
branch extension and fusion. No author decision is pending.


## Synchronized branch extension and completion — audited at 2485 declarations

A synchronized component on a whole old-label branch now extends to the
ambient set with actual aperture-compatible components on all protected
pieces. Exact full-set selected and protected image identities produce
the next branch frame. Induction extends every whole finite synchronized
branch chain, preserving the local map on its branch and fixing every
outside VF coordinate. The original RV labels remain retained.

Every already prepared outside RV-pullback remains prepared under that
extension. A prepared branch with a prepared complement yields a complete
actual synchronized ambient preparation witness. These results provide
the branch-extension and completion operations needed in the global
release/fusion argument; they do not yet discharge that induction.

All 2485 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. Full
6.19 remains complete through VF arity two. The next work applies the
whole-program machinery to the actual coordinate fibres and constructs
the remaining global fusion. No author decision is pending.


## Coordinate fibres, joint foci and whole-program freezing — audited at 2550 declarations

Actual coordinate fibres have complete original-base templates and
inherit proper invariance, double bounds, RV-pullback geometry and
retained leading terms. Their required field support, nontrivial
valuation, smallness and definable Gamma persist after adjoining the
chosen VF parameters. Lower-dimensional synchronized fibre witnesses
now yield finite whole-program covers on the actual coordinate family.
Mixed templates reassemble as exact joint domains. Their continuous
family formulas give actual original-base joint focus maps with complete
graphs and continuous tail fibres.

Definable doubly bounded RV-pullbacks with bounded RV support are proper
invariant. A complete continuous focus graph constructs an actual
protected permitted component in any specified target coordinate.
For a target different from the parameter coordinate, finite freezing
preserves focus independence and leading terms, constructs the full
continuous graph and checks all current ambient and protected product
domains. Component formulas with a prepared old-label locus assemble
into these actual joint focus graphs.

Definable parameter substitution now commutes with complete finite
programs: transitions, every intermediate ambient and protected image,
admissibility and terminal preparation. Actual finite-disc freezing
preserves the full initial ambient and protected sources and substitutes
all remaining program data together. This addresses the need to keep
later focus domains valid when freezing a sequence.

All 2550 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. The
complete RV-data assembly and final global release/fusion induction
remain unfinished. Full 6.19 remains complete only through VF arity two;
no complete higher-dimensional claim or author decision is pending.


## Complete program RV-data and protected freezing — audited at 2646 declarations

The complete RV-data relation is constructed from the actual finite
program choices. It records every intermediate ambient and protected
leading-term image, each clipped actual active locus, coefficient RV
value and complete Gamma name. Nonzero unit tags pack the different
arities into one definable row. Equality of packed rows recovers every
constituent, and explicit unit markers recover formula choices even on
empty fibres. Every admissible program trace and each complete choice
row is separately doubly bounded. No initial uniform bound over the VF
parameter family is asserted.

Actual coordinate-fibre witnesses construct the finite choice family
and its data. The complete membership relation enters unary preparation
with unrestricted RV output, producing finite original-base freezing,
a synchronized unary preparation and its actual protected ambient lift.
Every current ambient and protected product check is retained. Equal
target labels fix the formula choice and all selected program data at
the frozen parameters. Whole-program substitution preserves their full
initial ambient and protected sources and terminal preparation.

All 2646 complete public declaration types and transitive axiom records
passed; only `propext`, `Classical.choice` and `Quot.sound` occur. The
remaining work includes the actual post-preparation uniform-bound
adapter and the global release/fusion induction. Full 6.19 is still
complete only through VF arity two. No author decision is pending.


## Original-base bounds on the frozen program data — audited at 2667 declarations

Complete RV rows constant on the actual prepared unary quotient now descend
through its full definable graph. The checked bounded Gamma-family theorem
gives one original-base named radius bounding every packed data row at the
frozen parameters. Exact packing then bounds every constituent of each selected
program trace with that same radius. This includes all intermediate ambient
and protected leading-term images, active loci, coefficients and Gamma names.
No uniform bound over the initial VF parameter family is assumed, and no chosen
VF representative is added to the base.

All 2667 complete public declaration types and their transitive axiom records
pass with only `propext`, `Classical.choice` and `Quot.sound`. This completes the
post-preparation uniform-bound adapter. The general release/fusion induction
remains unfinished; full Proposition 6.19 is still proved only for VF arity at
most two.


## Variable releases, label refinements and joint domains — audited at 2765 declarations

Old apertures may now vary with retained RV labels. Their full definable Gamma
graph constructs the actual whole-label annulus in a new permitted component
image. Same-leading-term coordinate replacement proves exact coordinate-bundle
factorization for the ambient and all compatible protected pieces. Their
projections are proper and doubly bounded; an actual projected synchronized
preparation lifts back with the released coordinate fixed. An old global VF
coefficient is not assumed.

Entire synchronized chains also lift through ordinary RV-label refinements in
the same VF dimension. The full commuting square identifies every literal
protected image; terminal preparation is preserved. Reassembled families now
use the actual old frozen parameter recovered by the inverse unary preparation,
including its dependence on retained labels. Complete leading rows prove their
joint pullback, double bounds, proper invariance and taggedness. The selected
rows and uniform original-base named bound are verified on that actual parameter
map. Formula choices give disjoint proper whole-label branches covering the
prepared unary target. Exact inverse ambient coordinates and a tagged-pullback
criterion for old-or-empty refinement fibres are compiled.

All 2765 complete public declaration types and transitive axiom records pass
with only `propext`, `Classical.choice` and `Quot.sound`. The full global fusion
induction remains unfinished. Proposition 6.19 remains complete only through
VF arity two; these constructions do not establish the full proposition.


## Actual joint transport and focus graphs — audited at 2816 declarations

The actual ambient unary inverse now identifies the full transported ambient
and every protected piece with its joint parameter family. The complete program
trace discharges initial row constancy, original-base bounds, proper invariance
and taggedness. The actual ambient is a constructed RV-label refinement, and
its selected protected sets equal the literal images of the original pieces.

The covered joint ambient and its protected pieces are proper: on each inhabited
old-label fibre, exact refinement equalities identify one entire new fibre.
Clopenness descends along those equalities before applying the original-base
named criterion. Any actual synchronized preparation on the covered joint
problem then lifts back to the actual ambient with those exact protected images.

Component formulas at the actual RV-dependent old parameter now give complete
original-base focus maps, independence in the target coordinate, the required
leading terms and continuous tail fibres. Complete clipped active rows construct
the actual whole-label focus locus. These results connect the data construction
to the next focus step; the continuity repair, successive aperture comparison
and finite fusion existence induction still need their final assembly.

All 2816 complete public declaration types and transitive axiom records pass
with only `propext`, `Classical.choice` and `Quot.sound`. Proposition 6.19 remains
complete only through VF arity two. No full higher-dimensional claim is made.


## Repaired indexed components and variable apertures — audited at 2864 declarations

One continuity repair now checks product domains for the unary parameter base,
the current joint ambient, and every protected piece. It freezes the actual
parameter map, retains complete RV rows and their uniform bound, preserves the
full restricted source sets, and keeps the remaining program admissible. The
actual repaired focus equals the original focus formula at that same updated
parameter. An actual permitted component with compatible protected restrictions
is constructed from this data.

Old coefficients are actual original-base definable maps, with their RV leading
terms and bound recovered from singleton data rows. Their products with the
joint focus construct complete Gamma graphs and named old aperture radii on
RV fibres. One named VF coefficient dominates both the constructed component
and all old coefficients. Exact local permitted components also imply joint
coordinate invariance at these variable old radii, retaining membership in the
actual protected piece and ambient pullback.

All 2864 complete public declaration types and transitive axiom records pass
with only `propext`, `Classical.choice` and `Quot.sound`. The finite global fusion
existence induction and arbitrary-active-coordinate branch assembly remain
unfinished. Full Proposition 6.19 is still proved only through VF arity two.


## Arbitrary-coordinate fusion branches — audited at 2916 declarations

Whole synchronized permitted chains now transport through VF coordinate
permutations and retained RV labels, preserving the exact full protected
images. Conjugation constructs an actual chain in the original coordinates;
a coordinate permutation is not added as a primitive operation. Actual
coordinate projections preserve proper invariance and double bounds.

The retained core and the variable-aperture released annulus now lift an
actual projected preparation witness in any active coordinate, including all
compatible protected pieces. Their full coordinate-disc saturation and
retained leading tag are proved directly. All 2916 complete public types and
transitive axiom records pass with only `propext`, `Classical.choice` and
`Quot.sound`. The finite global fusion existence induction remains unfinished;
full Proposition 6.19 is still proved only through VF arity two.


## Sequential fusion stages — audited at 3010 declarations

Finite component programs now have sequential presentations with exactly
unchanged complete transition graphs, admissibility, protected intermediate
sets and RV traces. Every transition preserves the actual sorts even outside
its admissible locus. Removing a prefix or freezing the parameter retains
local geometry, preparation and the same original-base named data bound.

Actual sources can carry arbitrary extra RV labels. The terminal case and
the regularization step construct their full protected images. Continuity
repair on the covered joint ambient ports to an actual permitted component
on this source, with compatible restrictions and exact source and protected
set equalities at the updated parameter. Actual indexed old coefficient maps
retain their values, RV leading terms and bound; coordinate stability also
transfers through the retained labels.

All 3010 complete public types and transitive axiom records pass with only
`propext`, `Classical.choice` and `Quot.sound`. The centripetal comparison,
three-branch induction and complete global fusion existence proof remain
unfinished. Full Proposition 6.19 remains complete only through VF arity two.


## Actual fusion component and branch comparison — audited at 3055 declarations

The actual first global centripetal component is now constructed from a
uniform local program family. Continuity repair updates the entire remaining
program, preserves every actual protected source, and identifies the actual
active locus and full focus with the local formula at the updated parameter.
One original-base named coefficient dominates every old local coefficient,
with all compatible protected restrictions constructed.

The old varying aperture is an actual complete Gamma graph, named over the
original base and retained labels. Actual source and protected-set invariance
at this radius construct the released-annulus data. Canonical retained tags
separate the new core, released old core and precisely the old noncore branch;
the selected actual maps agree with the old local maps on the latter.

All 3055 complete public types and transitive axiom records pass with only
`propext`, `Classical.choice` and `Quot.sound`. Remaining work includes the exact
residual next-program context, branch assembly and global dimension induction.
Full Proposition 6.19 remains complete only through VF arity two.


## Complete fusion-step assembly — audited at 3104 declarations

An actual global component followed by regularization now carries a literal
synchronized chain and exact full protected images. Its residual branch has
exactly the next local ambient and protected fibres, with all properness,
double bounds and ambient pullback conditions constructed. The actual lower
dimensional induction witness prepares both replacement branches in any active
coordinate.

Preparations on complementary retained-label branches now assemble into one
whole-source preparation. An actual outside-branch RV refinement transports
the second preparation, while preserving the first. Applied twice, this joins
the core, release and prepared residual into a complete actual one-step fusion
witness on the original source and original protected family.

All 3104 complete public types and transitive axiom records pass with only
`propext`, `Classical.choice` and `Quot.sound`. The finite-program induction,
initial fixed-choice adapters and outer dimension induction remain unfinished.
The complete numbered Proposition 6.19 is still proved only through VF arity two.


## Finite-program and formula-choice fusion — audited at 3132 declarations

The structural induction over finite component sequences is complete,
including identity prefixes, exact regularization prefixes and centripetal
three-branch replacements. Arbitrary program trees normalize with exactly the
same complete data. Actual endpoint preparation and protected leading-term
rows supply terminal cases without artificial identity padding.

Each prepared formula-choice base now has its actual prescribed whole program,
local geometry, all constant RV rows and an original-base named uniform bound.
Restriction of the actual parameter map and full protected family to that base
is exact. Finite disjoint choices assemble, and the actual unary lift is
precomposed to return a permitted synchronized preparation of the original
ambient and protected pieces.

All 3132 complete public types and transitive axiom records pass with only
`propext`, `Classical.choice` and `Quot.sound`. The outer dimension induction
and public higher-dimensional 6.19 adapters remain unfinished. Full numbered
Proposition 6.19 remains certified only through VF arity two.


## Complete Proposition 6.19 — audited at 3143 declarations

The outer VF-dimension induction is complete, uniformly in the original base
and VF support. Fibre instances adjoin the actual first-coordinate value and
retain smallness, nontrivial definable Gamma and the nontrivial field valuation.
The actual head projection supplies the unary preparation context; finite
program fusion and formula-choice assembly give the successor case.

`ProperPreparation.proposition_6_19` constructs one actual finite special
covariant bijection in every VF arity and arbitrary RV dimension, with literal
special restrictions and doubly bounded RV-pullback images for every protected
proper invariant piece. The finite family need not cover the ambient or be
disjoint. `PreparationFieldBase.proposition_6_19_vfGenerated` supplies the actual
manuscript field-base convention. Neither public result assumes a remaining
fusion or lower-dimensional preparation witness. The accepted Section 2 Gamma
background and the standing model/base hypotheses remain explicit.

All 3143 complete public types and transitive axiom records pass, allowing only
`propext`, `Classical.choice` and `Quot.sound`. Receipt:
`Section6/.scratch/audit-proposition-6-19-all-dimensions.log`. Earlier milestone
paragraphs are historical; their unfinished 6.19 boundaries are superseded here.
Measured preparation beyond arity two, higher standard contractions, remaining
head-start/degree adapters and complete unary matching remain unfinished.


## Original-base ordinary matching — audited at 3165 declarations

The checked pinned Section 5.2 export supplies ordinary unary preparations
with original-base graph certificates for every primitive. Naming only Gamma
values whose complete fibres are already definable over S adds no parameters.
The new adapters construct actual source, target and conjugated maps over S,
with both preparations retained, exact commutation, bijectivity, RV-pullback
images and forward/inverse RV contraction. These are ordinary special maps;
the complete finite-aperture special-covariant matching is still unfinished.

A definable unary map also takes any set with finite VF projection to another
set with finite VF projection, even when its RV fibres are infinite. Inverse
images of the zero VF coordinate therefore have finite VF projection. Full
proper preparation now also applies to arbitrary proper invariant sources in
every arity through their actual RV hull, with literal protected restrictions.

All 3165 full public types and transitive axiom records pass with only the
three standard logical principles. Receipt:
`Section6/.scratch/audit-original-base-ordinary-matching.log`. No further full
numbered result is claimed by these matching adapters.


## Actual paired graph fibres and ordinary exceptions — audited at 3211 declarations

Every zero event of an ordinary unary chain pulls back to an original-base
definable exceptional set with finite VF projection. This includes every focus
event and does not require finite RV fibres at intermediate stages. Pairing
under the actual bijection constructs a finite original-base VF center graph,
including the source and target exceptional sets and their images/preimages.

The actual scalar maps on fixed mixed graph fibres have complete partial
graphs, bijections, continuity, open sources and the required target bounds.
Weak concentricity therefore gives arbitrarily small paired centered discs.
Their equality is proved for the full mixed source and target sets, retaining
both old RV tuples and including the actual center points. The old labels add
only finite tuples for the local analytic proof; their smallness is explicit.

When an actual permitted focus misses its current source its core is empty,
and its point map is the ordinary translation with a retained false label.
The corresponding unary finite-aperture component is constructed. Full scalar
graphs of ordinary foci, independence from VF inputs at fixed labels, and their
leading terms are also constructed over S. Global finite-aperture assembly
and complete 6.38 remain unfinished.

All 3211 full public types and transitive axiom records pass with only the
three standard logical principles. Receipt:
`Section6/.scratch/audit-mixed-paired-discs-and-chain-exceptions.log`.


## Complete ordinary-chain conversion off exceptions — audited at 3237 declarations

Actual ordinary foci pull back to proper current sources with arbitrary extra
RV labels and full original-base scalar graphs. Their active loci are whole
current label fibres. Avoidance of the constructed ordinary-chain exceptional
set proves the lifted focus graph misses the current source. Actual permitted
finite-aperture components therefore have empty cores and exactly the old VF
map; all old labels pass through explicit selectors.

The canonical and centripetal successor frames are constructed on the actual
regularized images and retain properness, double bounds, taggedness and the
complete old point map. Structural induction over the entire finite ordinary
chain now constructs one actual special-covariant realization off its
exceptional set, with exact complete endpoint commutation. This does not infer
RV-pullback geometry for an arbitrary restricted endpoint.

All 3237 complete public types and transitive axiom records pass with only the
three standard logical principles. Receipt:
`Section6/.scratch/audit-ordinary-chain-covariant-realization.log`. Complete
6.38 still requires the paired exceptional cores and whole matching assembly;
full 6.19 remains complete in all arities.


## Finite center separation and paired boundary offsets — audited at 3271 declarations

A complete special-covariant prefix now distinguishes every point of a finite
exceptional set by its retained RV labels. A common original-base named bound
on all nonzero root/focus differences makes each aperture core contain at
most one root per label. The terminating root induction retains those core
labels and separates the remaining roots. Properness, double bounds,
taggedness and the ambient RV-pullback are preserved. The actual VF centers
then descend to full original-base definable maps on their RV labels.

Paired whole-disc images now retain the same pointwise radius law. The target
offset is the actual difference f(a+d)-f(a), with any prescribed source and
target radius floors. This also holds on the full mixed graph fibre with both
old RV tuples retained. A focus on the boundary is absent from its core, and
its translation maps that entire core onto the corresponding nonzero RV disc.
Finite-prefix uniform named thresholds and finite full matching parameters
are also checked.

All 3271 complete public types and transitive axiom records pass with only
the three standard logical principles. Receipt:
`Section6/.scratch/audit-finite-center-separation-and-paired-offsets.log`.
Complete 6.38 still requires the permitted paired-core components, the
outside whole-disc geometry and global matching assembly. Full 6.19 remains
complete in every arity; these supporting declarations are not a complete
Section 6 claim.


## Actual prepared core neighborhoods — audited at 3310 declarations

Whole core fibres now have actual permitted boundary-focus components and
regularized special-covariant chains. Their images are exactly full nonzero
RV-discs with the branch flag and every old label retained. Equality of old
labels is preserved in both directions, so a paired-core bijection still
matches whole fibres under the literal conjugation, including all centers.

The actual offset-core domains are defined over the original base and proved
proper using their clopen fixed-label fibres. Their bounds and center/offset
maps are inherited from the ambient source. On an RV-pullback ambient source
their fibres are exactly the intended centered discs. A named VF coefficient
can be chosen beyond any prescribed named floor; the resulting core domains
contain every separated center and have explicitly constructed special
preparations. Finite full real parameter domains also admit one original-base
named eventual Gamma threshold and VF coefficient, without naming individual
parameters or local cutoffs.

All 3310 complete public types and transitive axiom records pass with only
the three standard logical principles. Receipt:
`Section6/.scratch/audit-boundary-core-preparations.log`. Full 6.38 remains
unfinished: the outside whole-disc geometry, compatibility of the separating
prefix with the ordinary conversion, and global assembly are still required.
These constructions do not assert that an arbitrary restricted ordinary
endpoint is an RV-pullback, or that an inverse special prefix is special.


## Ordinary outside geometry and covariant RV-pullback realization — audited at 3362 declarations

All intermediate ordinary zero events are exactly the inverse image of the
terminal zero coordinate. A bijective unary ordinary RV matching between
RV-pullbacks preserves zero fibres in both directions. Consequently the
actual source and target exceptional sets are already paired by the original
bijection; their paired enlargement adds no centers.

Unary ordinary chains are locally translations on every original RV fibre,
including zero points. Sufficiently small cores at their zero-event centers
have full RV-pullback images, proved from the exact unary difference law and
surjectivity onto the ordinary RV-pullback target. The full ordinary complement
image equals the target minus the union of those core images and is therefore
an RV-pullback. One geometric threshold works for every center in a finite
family and every choice of radii beyond that threshold.

The full covariant conversion now carries a constructed endpoint label
certificate. For a faithful original input frame, a proved ordinary
RV-pullback image yields an actual proper, doubly bounded RV-pullback endpoint,
with the exact VF map and complete old-label selector. Every extra retained
label is accounted for. Actual proper core complements and their complete
ordinary-chain conversions are constructed as well.

All 3362 complete public types and transitive axiom records pass with only
the three standard logical principles. Receipt:
`Section6/.scratch/audit-ordinary-outside-pullback-realization.log`. Complete
6.38 still requires uniform actual paired-core data, compatibility with the
center-separating construction, and global assembly. These new results are
supporting constructions and do not constitute a complete Section 6 claim.


## Uniform named paired-core coefficient — audited at 3403 declarations

The actual varying-coefficient boundary map evaluates the source point and
its target offset under the original bijection. Its complete graph, with
both old RV tuples retained, is definable over the original base. A fully
quantified formula expresses equality of the whole paired discs, including
all source and target points and the centers.

For every finite actual center family, all sufficiently small coefficients
satisfy this formula simultaneously. The good-coefficient set is defined
over the original base by projecting the bad parameter pairs. An eventual
VF choice argument then supplies one original-base named positive coefficient
that works at every center. No center is named individually, and no arbitrary
target-radius representative is assumed definable.

All 3403 public declaration types and transitive axiom records pass; only
`propext`, `Classical.choice`, and `Quot.sound` occur. Receipt:
`Section6/.scratch/audit-named-paired-boundary-coefficients.log`.
Complete 6.38 remains unfinished: these actual paired cores must still be
made compatible with the center-separating and complement preparations and
joined into the required global special-covariant preparation. Full 6.19
remains complete in every VF arity; no further numbered result is claimed.


## Paired radius floors and whole-ambient core branches — audited at 3438 declarations

The actual source and target offset maps now satisfy arbitrary two named
radius floors while retaining the full scalar and mixed paired-disc image
equalities. Their original-base graphs come from fixing the constructed
named coefficient in the varying-coefficient evaluation.

For a label-definable center and offset family, a permitted boundary
component is now constructed on the whole ambient RV-pullback. Its own
aperture misses every selected core; points outside those cores may use it.
The literal core image is a full RV-pullback, as is the literal complement
image. After regularization the core is detected by an actual original-base
set of RV tags, and final core-label equality is precisely old-label
equality. `AmbientCorePreparation` contains the whole permitted chain,
properness, double bounds, both image geometries, and the label certificate.
This does not glue independently constructed maps on unlabelled pieces.

All 3438 public declaration types and transitive axiom records pass with
only the three standard logical principles. Receipt:
`Section6/.scratch/audit-uniform-paired-cores-and-ambient-preparation.log`.
Full 6.38 still requires compatibility of these ambient core preparations
with the ordinary complement matching and the final matching assembly.
No additional complete numbered result is claimed at this milestone.


## Actual paired ambient core matching — audited at 3478 declarations

Offsets now descend to the separated old RV center labels over the original
base, on both sides of the original bijection. The actual definable core
domains have explicit center-incidence formulas. Their full source and
target unions are carried onto one another by the original bijection,
including all centers. Its literal restriction is a bijection of whole
old-label fibres when both center labelings are separated.

That matching survives the constructed whole-ambient special preparations
and agrees with the restriction of the same global conjugation. The public
`exists_named_finite_paired_core_preparation` constructs all offset choices,
smallness bounds, both whole-ambient chains, the actual core map, whole-core
fibre matching and center containment for every finite separated paired
center family. It does not assume these as unnamed preparatory data.

All 3478 complete public declaration types and transitive axiom records pass
with the three standard logical principles. Receipt:
`Section6/.scratch/audit-paired-ambient-core-matching.log`.
Full 6.38 still requires compatibility with the ordinary complement matching.
The new conditional ramified-value calculation checks a direct aperture
realizability issue; it is not a counterexample to arbitrary full matching
preparations. No definition or numbered statement is changed by this check.


## Author query S6-A1 — paired-aperture realizability (pending)

The checked whole-disc offsets and actual paired ambient preparations do
not yet justify the direct replacement of every ordinary focus by the
paired apertures asserted in the 6.38 proof. Definition 6.11 specifies one
original-base named coefficient per component. Over the allowed henselian
base C((t)), a square-root focus has value 1/2 while a unit focus has value
0. Direct apertures at these foci using globally named coefficients have
values m+1/2 and n, respectively, and cannot be paired for a translation
with unit Jacobian. The abstract value-group incompatibility and its VF
product adapter are compiled and audited in RamifiedApertureValues.

This is an obstruction to the direct construction in the supplied proof,
not a counterexample to all possible longer preparations. In particular,
no unproved residue-Euler or value-coset invariant is claimed. No definition,
parameter base or theorem statement has been changed. The separate review
copy shows the current Definition 6.11 and full Lemma 6.38 proof with the
new query in dark orange. The author must decide whether the intended
notion permits a finite original-base definable family of aperture
coefficients indexed by the retained RV labels, or retains the literal
global-coefficient definition and requires another construction. A finite
family permission would also need to be reflected in the Section 7 duality.

Review PDF: output/pdf/section6-paired-apertures-review.pdf (five pages of
manuscript context: printed pages 62, 63, 79–81). All five pages visually
checked. The approved shared manuscript and its revised PDF are unchanged.


## Finite-image measured preparation in every positive degree — audited at 3491 declarations

Actual Gamma forms with finite image now admit measured preparation in every
positive VF arity and arbitrary RV dimension, from arbitrary proper invariant
sources. Every value of the actual finite Gamma image is proved definable over
the original base, using the checked finite-order Gamma export. Its level set
is an actual original-base DefSet with proper geometry derived from uniform
level invariance. These level sets and every original protected set are
prepared by the same constructed finite special-covariant map. An auxiliary
finite proper cover that is constant on each piece's old-label fibres also
suffices; it need not coincide with the protected family.

The finite-partition statement, actual VF-generated field-base adapter and
selected-piece measured RV lifts are checked in every positive degree. The
selected lifts use exactly the ambient map, with finite RV fibres required
only on each selected original piece. Neither the ambient nor an auxiliary
RV hull is assumed to have finite RV fibres. The full audit of 3491 public
declaration types and transitive axiom records passes with only the three
standard logical principles; receipt:
`Section6/.scratch/audit-finite-image-measured-existence.log`.

This is an additional case of 6.21. A general proper Gamma form can have
infinite image, even on one old RV-disc, so the finite-image hypothesis is
not silently inferred. General higher-dimensional measured preparation,
ordered standard contractions, remaining head-start adapters and full 6.38
remain unfinished. Author query S6-A1 remains pending and the definition is
unchanged.


## Measured local programs and exact freezing — audited at 3533 declarations

The full first-order terminal Gamma-constancy test now has exact semantics
for actual transition and Gamma maps, using complete Gamma representatives
over the original base. Whole synchronized measured preparations promote
to this test; genuine saturation then supplies a finite original-base
program family from local witnesses. Measured-admissible programs realize
the actual form with exact transport, all restrictions and a tagged
measured target after regularization. Parameter substitution transports
the entire program and Gamma graph together. Simultaneous product domains
for every Gamma level imply equality of the complete frozen Gamma map
with the original map, including infinite-image forms.

Actual unary measured root iteration now retains the stronger synchronized
chain, including the common coordinate, coefficient and focus on every
protected piece. Actual head-fibre Gamma maps adjoin exactly the VF head;
their open levels and one complete original-base graph template are
constructed. In two dimensions the actual unary theorem discharges every
local witness needed for finite measured fibre-program selection.

All 3533 complete public declaration types and transitive axiom records
pass with only propext, Classical.choice and Quot.sound. Receipt:
`Section6/.scratch/audit-measured-program-selection.log`. This extends
the supporting infrastructure for general 6.21; higher-dimensional
measured fusion has not been assumed or completed. Full 6.38 and
S6-A1 remain as previously recorded.


## Measured aperture branches and component form compatibility — audited at 3562 declarations

The actual Gamma form on a released annulus is inverse transport through
the new permitted component, restricted to the actual branch. If the old
contracted core lies inside a uniform form-constancy radius, that form
descends through the same coordinate projection as the protected pieces.
The analogous retained-core form also descends. The released and retained
forms have proper level geometry, and their actual projected forms have
open levels; individual Gamma values need not be named.

A positive-dimensional measured preparation on a projected base now lifts
through the full retained-label VF disc, preserving the synchronized
chain, exact form values, all literal protected restrictions and the
carried coordinate everywhere. Both actual aperture branches have these
measured replacement adapters. These are induction steps with the
lower-dimensional preparation witness explicit.

Complete Gamma graph transport through an actual transition has checked
first-order image semantics: for a bijection it is precisely inverse
composition, on all representatives. It commutes with parameter
substitution. The semantic condition needed for aperture changes is now
explicit: the current Gamma form is constant in the active coordinate
inside each contracted core. Actual uniform form radii imply this
condition in any arity; coefficient refinement and compatible protected
restrictions preserve it. The actual unary measured root iteration
retains this condition at every component, together with synchronized
aperture data and exact intermediate form transport.

All 3562 complete public declaration types and transitive axiom records
pass with only the three standard logical principles. Receipt:
`Section6/.scratch/audit-measured-aperture-form-compatibility.log`.
Full higher-dimensional measured fusion, ordered standard contractions,
remaining head-start adapters and full 6.38 remain unfinished. S6-A1 is
still pending and no definition has been changed.


## Complete component form tests and unary ambient preparation — audited at 3592 declarations

The contracted-core form condition now has an original-base definable
parameter test, with exact semantics on full actual transition graphs
and on actual permitted centripetal components. Recursive program guards
transport every intermediate Gamma graph and commute with parameter
substitution. Actual form-compatible synchronized chains promote to these
guards, and admissible guarded programs construct actual form-compatible
chains. Thus the finite selection retains the component condition, in
addition to terminal measured constancy and prepared protected pieces.
The binary head-fibre family is constructed from the actual unary theorem.

The preliminary unary base preparation also now has a constructed
form-compatible lift in an arbitrary VF ambient, protecting arbitrary
proper pieces. At each step the common original-base named coefficient
lies above the uniform radius for all Gamma levels. The terminating
unary root process transports the complete ambient form through its
actual maps and retains the component condition throughout. This
discharges the preliminary ambient-form step; it is not an assumed
compatibility input.

All 3592 complete public declaration types and transitive axiom records
pass with only the three standard logical principles. Receipt:
`Section6/.scratch/audit-form-compatible-programs-and-context.log`.
General measured finite-program fusion, higher ordered standard
contractions, remaining head-start adapters and full 6.38 remain
unfinished. Author query S6-A1 is pending; no definition has changed.


## Measured traces, freezing and branch support — audited at 3662 declarations

The complete terminal Gamma graph now has a bounded RV trace retaining
all representatives. It is packed with every geometric program row and
formula-choice marker. Equality of packed rows recovers all those data,
and the actual Gamma values when terminal labels agree. Actual finite
head programs and their disjoint choice partition carry this record.

Finite freezing now preserves every Gamma level and the actual full
form. Its unary data preparation has a form-compatible ambient lift
above both the data-row and Gamma radii. An actual original-base named
uniform bound is constructed after unary preparation, without an initial
uniform VF-parameter bound. The complete older geometric record is
recovered, allowing the existing geometric constructions to be reused.

Retained-core and released-annulus form descent now follows directly
from semantic core constancy. Complete carried-coordinate chains,
actual measured preparations and the projected branch replacements
retain form compatibility and exact intermediate forms. Whole-label
component and finite-chain extensions retain it on the full ambient.

All 3662 complete public declaration types and transitive axiom records
pass with only the three standard logical principles. Receipt:
`Section6/.scratch/audit-measured-traces-freezing-carrying-and-tag-extensions.log`.
Complementary-branch measured assembly and general measured program
fusion remain unfinished, as do the higher standard contractions,
remaining head-start adapters and full 6.38. S6-A1 is pending; no
definition has changed.


## Measured branch gluing and one full fusion step — audited at 3713 declarations

Measured preparations and their component form condition now survive
arbitrary RV-label refinement and VF-coordinate reordering, with literal
permitted chains in the original coordinates. Preparations on two
complementary whole-label branches glue into one actual measured ambient
preparation with exact intermediate form transport.

Semantic form constancy in any active coordinate gives an original-base
Gamma descent with open projected levels. Lower-dimensional measured
induction now prepares both the retained core and the variable
old-aperture annulus, in every active coordinate and with every protected
piece. The old aperture is allowed to vary with retained labels; it is
not replaced by a fixed globally named coefficient.

One full measured fusion step is constructed from those two branches
and an actual preparation of the remaining-program residual. Its actual
global component, all literal images and complete form-compatible chain
are retained. Local component core constancy implies variable old-core
constancy, and the actual coefficient dominance implies the corresponding
condition on the smaller global core.

All 3713 complete public declaration types and transitive axiom records
pass with only the three standard logical principles. Receipt:
`Section6/.scratch/audit-measured-branch-gluing-and-single-fusion.log`.
The full finite-program iteration and outer dimension induction for
general 6.21 remain unfinished. Higher standard contractions, remaining
head-start adapters and full 6.38 also remain unfinished. S6-A1 is pending;
no definition has changed.


## Measured continuity repair, prefixes and terminal cases — audited at 3761 declarations

Sequential normalization retains every component form guard and the full
terminal Gamma trace. Selected-label form descent is constructed over
the original base with open levels. Continuity repair freezes every level
and preserves the actual source form when its parameter changes.

Uniform measured program families retain full form graphs, open levels,
component guards and measured row bounds under freezing and prefix
removal. The repaired local guards imply both the variable old-core and
the new global-core form conditions. Full terminal Gamma rows recover
values across different head parameters with the same retained labels;
the actual identity and regularization terminal preparations now retain
the complete form-compatible ambient chain.

All 3761 complete public declaration types and transitive axiom records
pass with only the three standard logical principles. Receipt:
`Section6/.scratch/audit-measured-continuity-prefixes-and-terminals.log`.
Full measured finite-program iteration and outer dimension induction
remain unfinished, as do higher standard contractions, remaining
head-start adapters and full 6.38. S6-A1 remains pending.


## Complete measured finite-program fusion — audited at 3777 declarations

The finite measured fusion theorem now handles every finite program tree.
Its sequential induction constructs all actual residual forms, open levels,
exact local/global form agreements and literal protected images. Terminal
Gamma traces compare different head parameters; component guards derive
both aperture form conditions. Arbitrary program normalization retains the
complete measured record and every intermediate form guard.

The sole dimension premise is actual form-compatible measured preparation
in the lower VF dimension. No residual preparation, continuity-repair form
condition or aperture form condition is accepted as an external input.
Whole formula-choice assembly and outer dimension induction remain before
general 6.21 is complete. Higher standard contractions, remaining head-start
adapters and full 6.38 remain unfinished; S6-A1 is pending.

All 3777 full declaration types and transitive axiom records pass with only
the three standard logical principles. Receipt:
`Section6/.scratch/audit-full-measured-finite-program-fusion.log`.


## Full Lemma 6.21 — audited at 3792 declarations

Measured preparation is now complete in every positive VF arity and
arbitrary RV dimension, for arbitrary Gamma images. The separate
zero-arity theorem completes the zero-dimensional case. The public
`lemma_6_21` and `lemma_6_21_vfGenerated` retain the actual finite proper
cover and give every selected finite-RV-fibre piece its degree-matched
measured RV lift through exactly the same ambient map.

The strong doubly bounded RV-pullback theorem constructs a complete
form-compatible synchronized chain. The proof includes measured finite
program fusion, actual form-preserving continuity repair, complete
terminal Gamma traces, finite formula-choice assembly and the outer VF
dimension induction. Each fibre instance adjoins exactly its actual VF
head. There is no finite-image hypothesis or external preparation premise.
Arbitrary proper sources use the already checked actual 6.19 preparation
and exact inverse transport of the full form.

All 3792 complete public declaration types and transitive axiom records
pass with only the three standard logical principles. The full Section
build passes 11321 jobs. Receipt:
`Section6/.scratch/audit-full-measured-6-21.log`.

Full Section 6 remains in progress: higher ordered standard contractions
in 6.27, remaining head-start/degree adapters and full unary matching 6.38
remain unfinished. S6-A1 is resolved: retain globally S-named coefficients and seek another construction. The aperture definition is unchanged.


## Author decision S6-A1 — retain the existing relative coefficients

The author confirmed, after explicitly reopening an accidental earlier
selection, that aperture coefficients must remain globally S-named as in
Definition 6.11. Seek another proof construction for 6.38. No RV-indexed
coefficient enlargement or corresponding dual-blowup definition change
is authorized. The direct paired-aperture obstruction remains a check
on that route only, not a counterexample to 6.38.


Clarification after S6-A1: the actual aperture radius in Definition 6.11
is polydisc-dependent: gamma_p = rad(pr_1 p) + gamma, and
 t_p = t * rv(pr_1 p). The author emphasized this dependence. References
to a global aperture were imprecise; the fixed data in the query were
the relative offset gamma and multiplier t (and its chosen lift c).
Current Lean data already use the varying cutoff v(c * focus), including
the RV-polydisc radius. The direct ramified-value calculation includes
that variation and is not a full matching obstruction. Recheck the
assembly route against this distinction; do not infer a need to enlarge
the definition from the calculation alone.


### Clarification of polydisc dependence

The aperture in use varies with the RV polydisc: the actual radius is
`rad(pr₁ p) + γ` and the actual RV point is `t · rv(pr₁ p)`. The fixed
data are the relative offset and multiplier, not the resulting cutoff.
The formalized cutoff `v(c · extendedFocus)` already retains this
dependence. Earlier references to a “global aperture” were imprecise;
they meant a named relative coefficient. No change to Definition 6.11
is requested or made on this account.


## Ordered contraction lifts — audited at 3854 declarations

A given actual ordered contraction program now constructs its full lift,
with a proper covariant homeomorphism, all original RV labels retained,
exact recovery of the final VF set from the contracted RV data, and total
Jacobian 1 outside a definable lower-dimensional set. Carrying previously
contracted coordinates preserves properness and the determinant.

Actual programs and full lifts exist in every VF arity for already doubly
bounded RV-pullback sources, in last-coordinate-first order. The general
proper-source construction in any prescribed order remains open; this
support does not claim full 6.27. The complete audit passed for 3854 public
declaration types with only the three recorded logical axioms.
Audit: `Section6/.scratch/audit-ordered-contraction-lifts.log`.


## Head-start degree and forms — audited at 3898 declarations

For a given actual ordered contraction program, every head start k now
has its actual RV object in degree n+k. Finite volume is proved from
finiteness of the source RV fibres over the selected old RV head. The
whole lifted map fixes the added VF coordinates, retains proper covariant
homeomorphism and double bounds, and has total Jacobian 1 off the literal
lift of a lower-dimensional exceptional set. Gamma forms descend through
the actual quotient with exact pointwise transport.

These adapters do not supply the remaining general prescribed-order
program existence or the final measured relative-stage assembly. Full
6.38 also remains unfinished. The complete audit passed for 3898 public
declaration types with only the recorded logical axioms.
Audit: `Section6/.scratch/audit-ordered-head-start-degree-and-forms.log`.


## Binary ordered contractions — audited at 3946 declarations

The binary last-coordinate-first case now exists for every doubly bounded
proper source, with arbitrary RV arity and no RV-pullback hypothesis.
`exists_binary_contraction_stage` constructs the actual first stage;
`ordered_standard_program_binary_doublyBounded` constructs the two-stage
program, and `lemma_6_27_binary_doublyBounded` supplies its full lift.

The proof retains a final-label base-displacement certificate throughout
the complete binary root iteration. An actual definable inverse supplies
the complementary restoration, which preserves proper homeomorphisms,
full last-coordinate RV-disc fibres and the approved total Jacobian.
The second stage uses the already complete unary theorem. No preparation
or displacement certificate is an external input to this binary result.

Higher-dimensional existence, the general coordinate-order and preliminary
normalization adapters, measured ordered-stage assembly, and full 6.38
remain unfinished. The complete audit passed for 3946 public declaration
types, with only the three recorded logical axioms.
Audit: `Section6/.scratch/audit-binary-ordered-contractions.log`.


## Full binary contraction existence — audited at 3987 declarations

`BinaryStandardContractionExistence.lemma_6_27_binary` constructs an actual
binary standard-contraction object for every proper source and every
coordinate order, with arbitrary RV arity. It includes exactly the
preliminary zero-centered normalization permitted in the manuscript,
the two-stage program, and its full lift on the original source.

The full lifted map is a proper covariant homeomorphism, has doubly bounded
RV-pullback target, recovers that target from its actual contracted RV data,
and has total Jacobian 1 outside a definable lower-dimensional set. The
coordinate relabelings are actual maps whose determinants cancel. The
`OrderedStandardContractionLift.ordered` field now records the exact
recursive composition of the prescribed stages and their carried maps.

This completes the binary dimension case, not general 6.27. Existence in
VF dimension at least three, measured ordered-stage assembly and full
unary matching 6.38 remain unfinished. The full audit passed for 3987
public declaration types with only the three recorded logical axioms.
Audit: `Section6/.scratch/audit-full-binary-any-order-normalized-contractions.log`.


## Binary measured ordered contractions — audited at 4034 declarations

`NormalizedBinaryMeasuredContractions.binary_measured_contraction_any_order`
constructs a measured ordered contraction for every proper binary source,
every coordinate order and every actual Gamma form satisfying the stated
open-level hypothesis. Gamma images may be infinite. The permitted
normalization and coordinate changes retain exact source-form transport.

The result includes the actual ordered program, its stage-composition
certificate, the full lifted proper homeomorphism, an actual Gamma form on
the final RV target, pointwise source-form factorization, and the measured
VF Jacobian identity outside the approved lower-dimensional exception.
The complete binary measured root iteration retains the base-displacement
certificate; all final preparation labels survive the restoration and
the unary tail program.

Head-start measured RV objects for a given measured program are constructed
in every degree. The remaining work includes the relative-stage/head-start
assembly on the original source, contraction existence in VF dimension at
least three, and full 6.38. The complete audit passed for 4034 public
declaration types with only the recorded logical axioms.
Audit: `Section6/.scratch/audit-binary-measured-any-order-contractions.log`.


## Actual unary compositions and original-source head starts — audited at 4063 declarations

Every actual ordered contraction lift now has an explicit finite chain of
relatively unary proper covariant homeomorphisms. Each actual step retains
its prescribed old RV labels and has unit total derivative at generic
points. Carrying a retained-label VF disc commutes with identity and
composition as equalities of full definable maps. Consequently the same
finite composition carries every head-start block while fixing its added
VF coordinates throughout.

For a measured binary contraction in either coordinate order, the head-start
RV object and full lifted map now start directly from the original proper
source, including its actual preliminary normalization. Finite volume is
derived from the original source fibres over the selected old RV labels.
The target has degree 2+k, doubly bounded support and volume image, and
nonzero volume coordinates. The actual map lands in its literal RV lift,
fixes the added VF coordinates, transports the original Gamma form exactly,
and is a proper covariant homeomorphism with unit total Jacobian outside
the literal lifted lower-dimensional exception.

The full audit passed for 4063 public declaration types, with only
`propext`, `Classical.choice` and `Quot.sound`. Receipt:
`Section6/.scratch/audit-unary-chains-original-binary-head-starts.log`.
These results do not assert contraction existence in VF dimension at least
three. Intermediate double bounds for the explicit unary chains and their
transport through coordinate relabeling and preliminary normalization are
still being assembled. Full 6.38 also remains unfinished. Definition 6.11
is unchanged and its actual aperture remains polydisc-dependent.


## Full normalized finite unary assembly — audited at 4136 declarations

Actual ordered lifts now retain double bounds on every intermediate domain
of their finite relatively unary compositions. Conjugation by a VF
coordinate permutation carries each individual unary step, preserves its
coordinate condition and all old labels, and cancels the permutation
determinants in its total derivative. This constructs the actual original
coordinate map with its full bounded unary chain.

The preliminary zero-centered normalization now also factors into actual
relatively unary proper covariant homeomorphisms in every positive VF
arity. More generally, any retained-label proper homeomorphism whose VF
displacements are determined by its final RV labels has such a finite
factorization. Coordinate interpolation constructs every actual intermediate
map, proper geometry and unit total derivative. If both endpoints are
doubly bounded, all interpolated domains are doubly bounded too.

Combining these constructions gives the full original-source finite unary
chain for any given ordered program, including its normalization and
coordinate order. Every binary measured head-start lift therefore has its
actual full finite unary composition. When the original source is doubly
bounded, all intermediate domains are doubly bounded. For arbitrary proper
sources, the paper's preliminary normalization precedes the bounded ordered
stages, as stipulated.

The audit passed for 4136 complete public types and their transitive axiom
records, allowing only `propext`, `Classical.choice` and `Quot.sound`.
Receipt: `Section6/.scratch/audit-full-normalized-unary-head-start-assembly.log`.
Contraction existence in VF dimension at least three and complete 6.38
remain unfinished. No aperture definition or manuscript change was made.


## Protected ordered programs — audited at 4166 declarations

A finite family of proper invariant subsets now has actual bounded
membership labels over the original base. Their graft is a proper covariant
homeomorphism fixing every VF coordinate, with identity total derivative.
It is admitted as a standard-contraction operation; no special-covariant
bijection claim is made for this graft.

The graft is absorbed into the first actual contraction stage. Its target,
remaining stages and coordinate order stay the same; its full contraction
map is proved to be the old contraction composed with the graft. A new
actual lower-dimensional total-Jacobian exception is constructed on the
original source. Retention of the membership labels makes every protected
image an RV-pullback. The measured adapter transports the full original
Gamma form and its open levels through arbitrary retained-label selectors.
Actual protected binary programs are constructed in both variants.

The binary original-source head-start lift also has an explicit VF measure
identity against its actual degree 2+k measured RV object, actual label map
and original source form. All 4166 public types and transitive axiom records
passed with the same three allowed logical principles. Receipt:
`Section6/.scratch/audit-protected-ordered-programs.log`.
The higher-dimensional deferred-base construction and full 6.38 remain open.


## Generic base homeomorphisms through retained refinements — audited at 4206 declarations

Every bounded finite relatively unary homeomorphism chain now lifts through
an actual full RV refinement. The new target has whole old target fibres
or empty fibres, proper invariant geometry and double bounds. The actual
full map retains every refining label, commutes with the complete old map,
and preserves each generic unit total derivative. This construction also
carries an extra full retained-label VF disc pointwise fixed, retaining
all actual intermediate double bounds. It applies to any given bounded
ordered lift and uses no special-bijection input for the base map.

The finite-aperture geometry now includes exact images of both actual
clauses. Moving the focus and boundary offset without changing their
respective RV leading terms preserves each entire branch image. An actual
output point transports to the new focus with the same core branch.
The resulting cutoff remains polydisc-dependent as in Definition 6.11.

The full audit passed for 4206 public declaration types and transitive
axiom records with only `propext`, `Classical.choice` and `Quot.sound`.
Receipt: `Section6/.scratch/audit-refinement-carried-unary-lifts.log`.
Higher-dimensional ordered existence and full 6.38 remain unfinished;
the active-step refinement and deferred-base assembly are still required.


## Active full-disc steps over an unchanged base — audited at 4232 declarations

An actual active centripetal step on a full retained-label VF-disc bundle
has a projected base whose fibres are whole old base fibres or empty.
Changing the base point preserves the active output point, its core branch
and every final RV label. Independently, changing the active output within
its RV disc preserves those labels. Consequently the actual full target
is precisely the full retained-label VF-disc bundle over this base
refinement. The retargeted step commutes with the original base projection
and has a bounded finite relatively unary chain with the approved generic
unit total derivative.

The full audit passed for 4232 complete public declaration types and their
transitive axiom records. Receipt:
`Section6/.scratch/audit-active-carried-refinement-steps.log`.
These are actual transports for a given step. Restoring deferred base
transformations, higher-dimensional standard-contraction existence and
full Lemma 6.38 remain unfinished.


## Actual inverse-base restoration — audited at 4256 declarations

Actual inverse maps have generic unit total derivative whenever the
original definable bijection does. Retaining the complete source RV
tuple preserves a bounded proper covariant homeomorphism even without
an old-label selector; its target fibres are the actual fixed-label
graph ranges. Bounded retained base maps now compose, pull back through
new base homeomorphisms, port through full RV refinements and carry an
additional VF disc pointwise. The active-step restoration recovers the
complete earlier base tuple and leaves the active output unchanged.
Conjugating a given active step through an arbitrary such base map
therefore yields an actual bounded relatively unary homeomorphism with
all old labels retained and generic unit total derivative. No constant
RV-indexed base displacement is required.

The full audit passed for 4256 complete public declaration types and
transitive axiom records. Receipt:
`Section6/.scratch/audit-conjugated-active-base-restoration.log`.
These constructions apply to given actual base maps and active steps.
Higher-dimensional standard-contraction existence and complete unary
matching 6.38 remain unfinished.


## Continuous graph charts and stable shears — audited at 4298 declarations

One finite original-base freezing family repairs a finite collection of
scalar maps simultaneously and preserves every domain with the chosen
invariance radius. Fixed-label graph maps have actual definable scalar
charts and source indicators, with continuous zero extensions for proper
homeomorphisms. Displacement stability along inactive fibres constructs
actual shear charts and generic unit total derivatives. The unary
contraction has this stronger property, and the approved derivative
exception is constructed for any given such full-bundle map in every
arity. The displacement descends to an original-base definable map of
inactive coordinates and both RV tuples; its entire zero-extended RV
family is continuous. These are checked inputs to the strengthened
first-stage induction. Its higher-dimensional existence step, the
measured extension and complete Lemma 6.38 remain unfinished.

The full audit passed for 4298 complete public declaration types and
transitive axiom records. Receipt:
`Section6/.scratch/audit-shear-chart-family-descent.log`.


## Bounded open labels and actual branched stages — audited at 4356 declarations

An actual RV label map with open fixed-label fibres on a proper source
has a constructed uniform constancy radius, without assuming bounds on
its new labels. If these labels are nonzero, their support is doubly
bounded and their actual map is proper covariant. A continuous definable
source indicator and inactive-coordinate offset, with the exact unique
output-label and full-disc conditions, now construct an actual bijection
onto its actual image. Its fixed-label branches are global continuous
shears on clopen domains and have clopen ranges. The actual target fills
every active RV disc. The resulting contraction stage has constructed
proper covariance, all target bounds and the approved total-derivative
exception; these are not separate premises.

The full audit passed for 4356 complete public declaration types and
transitive axiom records. Receipt:
`Section6/.scratch/audit-open-label-branched-shear-contractions.log`.
Uniform selection and fusion of this continuous branch data from the
lower-dimensional stages are still required. Full contraction existence
in dimension at least three, its measured extension and complete unary
matching 6.38 remain unfinished.


## Extracted stage data and initial parameter loci — audited at 4386 declarations

Every actual strengthened stage now supplies its two full continuous
chart families, with the exact graph-source indicator, inactive
displacement, retained labels and full-disc closure. Its unary branch-data
witness is constructed for every proper unary source. Both complete local
graphs promote to templates over the original base while retaining the
actual parameter tuple, RV selectors and exact graph sections. Scalar
level relations and the complete binary-indicator parameter locus are
first-order definable, with checked bridges to the actual values on every
RV row and VF input.

The full audit passed for 4386 complete public declaration types and
transitive axiom records. Receipt:
`Section6/.scratch/audit-stage-extraction-chart-templates.log`.
The other admissibility loci, finite formula selection and common
continuity repair still need assembly into the higher-dimensional
existence step. Full higher-dimensional 6.27, its measured extension and
full 6.38 remain unfinished.


## Complete branch-data admissibility and finite selection — audited at 4461 declarations

All branch-data conditions are now first-order definable over the original
base: exact prescribed source, unique output labels, retained labels,
nonzero output, active leading term and full active RV-disc closure. The
combined good locus constructs actual continuous definable branch data
on exactly that source. Every actual local witness promotes into the full
locus using equality of its entire chart-family graphs. Saturation then
selects finitely many complete admissible templates, with their possibly
different RV output arities retained.

The full audit passed for 4461 complete public declaration types and
transitive axiom records. Receipt:
`Section6/.scratch/audit-full-branched-shear-admissibility-selection.log`.
Padding and selection of those templates and common continuity repair
remain to be assembled into the higher-dimensional existence induction.
Full higher-dimensional 6.27, its measured extension and full 6.38 remain
unfinished. Definition 6.11 is unchanged: the actual aperture depends on
the RV-polydisc through its radius and leading term.


## One selected branch-data template — audited at 4518 declarations

The finite local chart templates now share an actual common RV code. It
retains old labels, the active leading term and every local output block;
unused blocks contain the nonzero unit. Decoding and code validity are
original-base definable. Reindexing and finite RV and parameter case
distinctions preserve complete continuous graph formulas with exact
values. Padding preserves every admissibility condition. A disjoint
definable choice cover therefore constructs one chart pair over the
original base, continuous in its VF inputs at every fixed parameter and
fully admissible throughout the covered source family.

The full audit passed for 4518 complete public declaration types and
transitive axiom records. Receipt:
`Section6/.scratch/audit-common-selected-branched-shear-templates.log`.
Realizing this pair as joint head-parameter maps and applying one common
continuity repair remain before the higher-dimensional existence step.
Full higher-dimensional 6.27, its measured extension and full 6.38 remain
unfinished.


## Complete unmeasured standard-contraction existence — audited at 4565 declarations

**Complete numbered result: unmeasured Lemma 6.27 in every positive VF
dimension, every coordinate order and arbitrary RV arity.** The actual
object `StandardContraction` contains the permitted zero-centered
normalization, complete ordered program and full lift. Its map starts on
the original proper source. Its target is a proper doubly bounded
RV-pullback, with exact recovery from the final RV labels, a surjective
contraction and the approved almost-everywhere unit total derivative.
The separate zero-VF case has an actual program and lift.

The public constructor is `lemma_6_27` in
`section 6/StandardContractionExistence.lean`.
`lemma_6_27_doublyBounded` constructs the direct canonical ordered program
and full lift without a pullback hypothesis. Its first stages come from
`branched_shear_data_all_dimensions`: the original-base finite chart
selection, simultaneous freezing and exact semantic fusion are fully
constructed, and the dimension induction adjoins exactly the actual VF
head on each local fibre. No lower-dimensional stage or fusion witness
remains an external input to this existence theorem.

The full audit passed for 4565 complete public declaration types and
transitive axiom records. Receipt:
`Section6/.scratch/audit-full-unmeasured-standard-contraction-existence.log`.
The measured extension in dimensions at least three and complete unary
finite-aperture matching 6.38 remain unfinished. Section 6 remains in
progress. Definition 6.11 is unchanged.


## Complete measured standard-contraction existence — audited at 4600 declarations

**Complete unmeasured and measured standard-contraction existence 6.27
and the measured head-start construction in every positive VF dimension
and every coordinate order.** Arbitrary proper sources retain the actual
permitted normalization. Arbitrary Gamma images retain the stated open
fixed-label level hypothesis; no finite-image assumption is added. The
measured preparation's actual RV labels are grafted with every VF
coordinate fixed, absorbed into the first ordered stage, and retained
through the full program. The source form descends through its actual
surjective contraction map. Exact pointwise transport and the approved
almost-everywhere full measure identity are checked. Zero VF arity has
an actual identity measured program retaining the whole form.

The public measured constructor is
`NormalizedMeasuredContractions.measured_contraction_any_order`. The
canonical bounded-source constructors are
`measured_ordered_program_all_dimensions` and
`measured_ordered_contraction_all_dimensions`. Finite proper families
have actual simultaneous programs, both measured and unmeasured, in
every positive dimension. Every normalized measured contraction has its
actual degree n+k measured RV head-start object and full original-source
lift, finite volume derived from the original source, fixed added VF
coordinates, exact form transport, proper bounds and the approved
measure identity. Its finite relatively unary chain and intermediate
bounds are checked.

The full audit passed for 4600 complete public declaration types and
transitive axiom records. Receipt:
`Section6/.scratch/audit-full-measured-standard-contraction-all-dimensions.log`.
**Full unary finite-aperture matching 6.38 remains unfinished.**
No complete Section 6 claim is made. Definition 6.11 is unchanged; its
actual aperture varies with the RV-polydisc.


## Critical mathematical review S6-A2 — finite-preparation profile (pending)

A new candidate argument tests full Lemma 6.38 under the retained original-base aperture coefficients. It uses the exact polydisc-dependent cutoff, gamma_p = rad(pr_1 p) + gamma; no global absolute cutoff is substituted. The review PDF `output/pdf/section6-ramified-profile-review.pdf` reproduces the current Definition 6.11 and full 6.38 context on its first four pages, followed by three dark-orange pages containing the candidate argument. All three new pages were rendered and visually checked. The panel display request returned `queued`; visible-panel state was not observed.

Over the allowed henselian parameter field C((t)), a two-label piecewise affine measured bijection sends a full unit RV disc together with a bounded annulus onto a full unit RV disc. Its central branch has derivative value 1/2; the annular branch has derivative value 0. The proposed finite-preparation invariant is the residue Euler profile of leading radius plus transported form, summed by cosets of the named value subgroup Z. A full unary component would change the profile only by removing one point and adding one at a named integral increment; the full annular fibres contribute zero. The proposed initial invariants are 2[1/2 mod Z] and 2[0 mod Z].

This is **a candidate manuscript-level obstruction, not a completed Lean counterexample or an established nonexistence theorem**. The complete special-chain presentation/profile extraction and the full native ramified example have not yet been formalized. The residue conservation components for the explicit finite-curve presentations are now implemented; their complete audit is recorded separately below. The author was asked to review the finite-trace claim or identify a permitted operation it excludes. This is a new mathematical question beyond the old direct-aperture test S6-A1. No definition, theorem statement, main proof, or Section 7 source has changed. S6-A1 remains resolved as before. Independent checking continues while this review is pending.


## Unary finite-preparation checks — audited at 4635 declarations

The full build and complete public-type/axiom audit passed. Receipt:
`Section6/.scratch/audit-unary-finite-profile-components2.log`. Only
`propext`, `Classical.choice` and `Quot.sound` occur. Existing pins and
numbered-result scopes are unchanged.

Newly checked components for the candidate S6-A2 argument are:

- `UnaryActiveLabelFiniteness`: the finite focus image and finite source RV fibres force finitely many active old label tuples for each actual unary component; its focus point lies in the full source disc.
- `UnarySpecialPullbackTrace`: arbitrary actual finite special chains preserve unary RV-pullbacks and finite RV fibres.
- `ZeroCenteredBoundedTrace`: source invariance forces every zero-centered branch to be inactive on an already doubly bounded source; the VF map is the identity and only constant tags are added.
- `UnaryCentripetalDiscTrace`: exact full annulus/core images for every active old label, with the current-disc-dependent cutoff. The existing scalar branch-image theorem is reused.
- `NamedApertureWeightClasses`: individually S-named VF values generate an actual subgroup; the actual core radius times inherited form has the same class as the original disc weight.
- `FiniteApertureProfiles`: finite signed profiles preserve their coset signature under point replacements at subgroup increments; the ramified initial signatures are distinct.
- `FiniteExceptionalTagRigidity`: finite VF exceptions cannot alter the RV contraction of a unary proper covariant map, even when the comparison function has no continuity or definability premise.
- `ResidueCurveConservation`, `FiniteCurveExcisions`, `FiniteResidueCurveEuler` and `NativeFiniteResidueCurveEuler`: actual definable bijections of finite unions of native residue affine lines with finite holes and isolated points preserve their finite Euler count. The proof constructs finite excisions and uses the pinned algebraic-field conservation and native residue graph bridge; no Euler or HK axiom is introduced.

**These are supporting checks, not full 6.38 and not a complete formal
counterexample.** The complete actual special-chain presentation/profile
extraction and the full native ramified example remain unformalized.
The candidate manuscript argument is pending author mathematical review
in the dark-orange pages of `Section6/output/pdf/section6-ramified-profile-review.pdf`.
The PDF uses a sufficiently saturated extension with residue field k
extending C; the named base is C((t)). Its new pages were rendered and
visually inspected after the final wording correction. Definition 6.11,
the main manuscript and the author decision S6-A1 are unchanged.


## S6-A2 author follow-up — intuitive explanation and repair proposal

The author replied to the review question by asking for an intuitive explanation and a proposed solution. This is not approval of a definition or theorem change. The proposed repair is recorded in `output/pdf/section6-aperture-repair-proposal.pdf`: four unchanged manuscript-context pages followed by two dark-orange review pages. Both new pages were rendered and visually inspected.

The obstruction concerns the representable extra depth, not the existing dependence of gamma_p on p. Over C((t)), individually named VF multipliers have integral value, while an RV-labelled square root produces a half-integral derivative value. A direct source cutoff N needs a paired target cutoff N+1/2. The candidate finite-chain residue profile is intended to show that extra finite preparations cannot erase this mismatch; the complete trace extraction remains unformalized.

The recommended narrow extension keeps a single S-definable gamma per component but permits an S-definable finite-image VF coefficient map c(u) on retained RV labels, of constant value gamma. Set t(u)=rv(c(u)), gamma_p=rad(pr_1 p)+gamma and t_p=t(u_p)rv(pr_1 p), and use the lifted core translation a-lambda(x)+lambda(x)c(u(x)). Finite families with several coefficient valuations can first be partitioned by their finite, individually definable Gamma values. The example is explicitly repaired by c_A=t^N and c_B(u)=a(u)t^N, N>=1: source and target core cutoffs are N and N+1/2; the conjugate is multiplication by a(u) on the original central branch and the identity on the original annular branch, including the retained core tags. The entire family remains S-definable without globally naming an individual root.

Section 7's dual annular blowups would need the same finite-family representative convention, including the actual finite-image definable VF lift. This is a recommendation for review, not an incorporated change and not a completed full 6.38 proof. An algebraically closed VF parameter base removes this particular obstruction but restricts the statement's scope. No main manuscript, formal primitive, or Section 7 source has changed; the 4635-declaration audit remains the current Lean receipt.


## S6-A3 — downstream audit and the weaker 6.38 route

The author confirmed that t is fixed for all p, requested checking every downstream consequence of a proposed change to 6.11, and then suggested weakening 6.38 instead. The current recommendation keeps Definition 6.11 unchanged and investigates a weaker comparison of RV classes. No prior proposal to enlarge the primitive has been adopted.

The immediate application in Lemma 7.13 needs common blowup comparison, not the prescribed VF conjugate and commuting squares. At ring level, equality modulo the kernel ideal would suffice. However the downstream audit identifies a new, explicit test of that weaker requirement. Let U be the two RV labels of roots a^2=t over C((t)). Give U structural coordinate 1 and form 0. Let V be U times the full annulus 0<val(s)<=1/2 plus the separately tagged graph s=u, with structural coordinate s and form 0. The lifted sets are isomorphic by the actual clopen translations y=x-1 outside the half-radius core and y=x-1+a(u) inside, retaining u, rv(y) and a nonzero branch tag. Both derivatives are 1. This uses the original VF category and does not assume an enlarged special primitive.

Using the independent pure-RV h_2 construction from Lemma 8.2 and the usual Euler characteristic on its variety coefficients, every old scalar generator P_N has group-ring image delta(-2N)-delta(0). The relative relation [V]-[U] has image 2*(delta(-1)-delta(0)). The quotient Q -> Q/(2Z) kills all former images and not the latter, even with arbitrary ring coefficients. Thus, at manuscript level with that independent h_2 invariance retained, the relative relation is outside the old scalar ideal while its VF lifts are isomorphic. The old kernel statement cannot simply be certified unchanged after weakening 6.38. The complete native h_2 bridge and concrete ACVF example are not yet formalized here; this is not claimed as a complete Lean counterexample.

The example behaves better after the final specialization: h_2([V]-[U])=[mu_2]*(L*T^-1-1), which vanishes under T->L. In a general m-rational trace, definability of the endpoint over the original base gives m-rationality by functional closure. On a nonempty constant-depth piece m*gamma is integral, and the finite annular factor telescopes to (L*T^-1-1)*sum(T^-i). This supports pursuing a corrected relative kernel without automatically changing the final specialization values. The full relative-family trace formula and the natural-subring intersection still require proof.

The reviewed proposal `Section6/output/pdf/section6-downstream-aperture-audit.pdf` contains eight unchanged context pages and four orange audit pages. Its new pages were rendered and visually inspected; formal tags 0/1 are explicitly encoded by nonzero named RV constants and the canonical leading term is included in the displayed lift map. `Section6/reference/aperture-downstream-audit.json` records the source hash and the dependency matrix through all of Sections 7 and 8. The matrix distinguishes unaffected statements, changes to the kernel target, new uniform-witness obligations and pre-existing independent proof gaps. It does not certify all downstream results as complete.

A localized weaker 6.38 could compare degree-one RV classes modulo an explicitly defined relative annular congruence. Its homogeneous ideal would replace the old scalar ideal in the kernel/ring target only after author review and proof. A merely fibrewise finite VF coefficient family is not automatically closed under higher-dimensional witness uniformization: more general bounded RV endpoint data and actual lifts over inactive VF variables may be required. No global RV-to-VF section is assumed.

**Checked algebraic support.** `DownstreamApertureIdealTest` proves the group-ring quotient, scalar ideal containment in its kernel, nonmembership for an endpoint in another coset, and the pullback theorem with its ring-specialization premise explicit. `FiniteApertureSpecializationFactors` proves the finite geometric factorization, vanishing under inverse substitution, and the integer/ramified two-label test values. These are 13 new supporting declarations. The full audit passed at 4648 complete public types and transitive axiom records, with the same three standard logical principles and unchanged pins. Receipt: `Section6/.scratch/audit-downstream-aperture-ideal-and-specialization.log`. No full Section 6, Section 7 or Section 8 claim is made. No main manuscript, Section 7 source, or accepted definition has changed.


## S6-A4 — precise proposed local repair, keeping Definition 6.11

The author asked for an intuitive account of the missing kernel relation and the smallest repair of 6.38 and Theorem 7.26 with Definition 6.11 unchanged. This is a request for a proposal, not approval to edit either statement. The new review PDF is `Section6/output/pdf/section6-relative-kernel-repair.pdf`: seven unchanged context pages and three dark-orange proposal pages. All three new pages were rendered and visually inspected. The reusable, unapplied TeX draft is `Section6/reference/proposed-revisions/S6-A4-relative-kernel/proposal.tex`.

Intuitively, cutting a VF disc into an outer shell and an inner ball, then translating the inner ball to a nonzero RV disc, is volume preserving. Its RV description must remember the endpoint chosen from the retained label. A finite algebraic family can supply such labelled endpoints without supplying any one globally named endpoint. The root-label example requires the relation “outer annulus over U plus the separately tagged endpoint graph s=u equals U with structural coordinate 1”, with form 0 throughout. The endpoint denotes the entire translated VF ball, not a single VF point.

The proposed RV rule keeps the finite-to-one omitted-coordinate projection condition of Definition 7.2, but lets the endpoint be an S-definable function tau:U->RV with bounded nonnegative gamma(u)=vrv(tau(u)). Its domain is the disjoint tagged union of the full annulus 0<vrv(s)<=gamma(u) and the endpoint graph s=tau(u). Multiply the active structural coordinate f_j(u) by s and pull back the old form. Constant tau gives the original finite-aperture rule. This does not assume a global definable VF section of tau. Boundedness and the unchanged finite-to-one condition preserve double bounds, finite volume fibres and degree.

Let I_rel be the graded semiring congruence generated by these explicit RV pairs and J_rel the homogeneous ideal generated by their differences. The proposed weaker 6.38 asserts that standard contractions of two isomorphic degree-one measured proper invariant VF objects agree modulo I_rel, without prescribing a prepared VF conjugate or commuting diagram. The proposed 7.26 keeps its lifting characterization and replaces the semigroup quotient by I_rel and the graded-ring quotient by J_rel. Add the relative rule after 7.2 and make the corresponding comparison/generator updates in 7.13-7.25. Definition 6.11 and every original special transformation remain unchanged.

This is an explicit generator proposal, not the circular definition J_rel=ker(mu L). Before adoption one must construct proper measured lifts of all relative generators using finitary center lifting over inactive VF variables, prove the weaker unary comparison, uniformize full relative endpoint/comparison graphs in the fibrewise step, and redo the kernel induction. Section 8 still needs the full trace and natural-subring intersection arguments and the retraction factorization. The finite geometric specialization factor is already checked, but it does not certify the whole revised theorem. No mathematical statement in the main manuscript, accepted primitive, or Section 7 source has been changed. No Lean source changed in this proposal turn; the 4648-declaration audit remains current.


## S6-A5 — synchronized variable-aperture investigation

The author now asks to investigate allowing variable apertures in both
Definitions 6.11 and 7.2. This supersedes the prior working preference to
keep 6.11 fixed; it authorizes an investigation and a concrete review
proposal, not an assertion that the revised kernel theorem is proved.
The new proposal is `output/pdf/section6-synchronized-aperture-audit.pdf`:
five unchanged context pages and four orange pages 6–9. The reusable
unapplied draft is
`reference/proposed-revisions/S6-A5-synchronized-apertures/proposal.tex`;
the structured record is `reference/synchronized-aperture-audit.json`.

The coherent synchronized data are an S-definable nonzero RV function
tau(u) on retained labels, with one finite named upper bound on
0<=gamma(u)=vrv(tau(u)), and actual cutoff
gamma_p=rad(active RV disc)+gamma(u)>=alpha_p. The compressed endpoint is
tau(u) times the active leading term. The bijective VF lift requires a
definable continuous endpoint representative b(x,u) over the focus
domain, independent of the changing VF coordinate, with this leading
term. Its core clause is a-lambda(x,u)+b(x,u). This admits the original
constant-coefficient primitives as a subclass.

Merely asking for a VF-valued function c(u) on the RV labels is too
restrictive for the uniform higher-degree formulation. For unit RV labels
u, structural map f(u)=(1,u), and tau(u)=rv(T)u, such a c(u) would give an
infinite-image RV-to-VF map. On the actual lift there is an inactive VF
coordinate a with rv(a)=u, so b(a,u)=Ta is continuous and supplies the
endpoint. No global RV-to-VF section or parameter-field enlargement is
used. On the RV side the original finite-to-one projection condition
implies finiteness over the inactive structural coordinates; finitary
source and endpoint center lifting must be performed over their full VF
representatives. In unary degree this reduces to finite algebraic
families. The root-label half-radius test becomes exactly one permitted
variable-aperture step with tau(u)=u and b(u)=a(u).

Direct manuscript-level checks: local branch maps and inverses are
triangular translations with determinant one generically; include the
bad loci of b alongside those of lambda in the approved AE argument.
The depth bound preserves double bounds. Fixed-label continuity and
open graph-fiber domains/ranges give the existing covariance route.
RV finite fibres are preserved because s is determined by u and the
new active structural coordinate, with at most two tags. Common
refinements partition by aperture valuation order and use t/r on the
shallower endpoint; the quotient has nonnegative bounded valuation and
the total weight is preserved. These are mathematical checks, not new
complete Lean certificates for the enlarged class.

Existing preparation and contraction existence witnesses in 6.19, 6.21
and 6.27 remain valid because original steps form a subclass. Universal
special-transformation assertions and the special/blowup duality need
the new variable-endpoint interface. The naming obstruction to strong
6.38 is removed, but the full finite-chain transport and matching proof
is still required. In 7.14, one must prepare the complete aperture,
locus and comparison graphs and obtain uniformly bounded witnesses;
allowing variables does not automatically discharge R125.

Define I_var by common variable-aperture blowups after the refinement
proofs, and define J_var explicitly as the homogeneous ideal generated
by all variable-blowup class differences. The graded-ring target of
7.26 must use J_var. The scalar factorization of 7.25 does not describe
an endpoint varying over the base, so it cannot be retained as the
complete generator proof. The introduction, Notation 4.13 interpretation,
comparison maps and later quotient displays also need corresponding
updates. The old scalar ideal remains a subideal; simply adding all
rational radii as unnamed scalar generators does not encode the
correlated endpoint family.

There is a more precise extension of the Section 8 argument. Retain the
entire endpoint graph in a compatible bipolar decomposition. Functional
closure at m-rational labels gives M=m*vrv(tau(u)) integral on every
nonempty fixed-valuation trace piece. Its correction has factor
(L-1)*sum(T^-r,r=1..M)+T^-M-1
=(L*T^-1-1)*sum(T^-r,r=0..M-1). The full equivariant family trace formula
must still be constructed; the finite identity is already Lean-checked.
Conditional on that formula, every h_m(J_var) lies in the single ideal
(g), g=L*T^-1-1, in the rational-exponent group ring. For x in the natural
subring write h_m(x)=gQ. Since g has integer exponents,
pr_0(gQ)=g*pr_0(Q), so the existing integer-exponent projection handles
arbitrary coefficients and evaluation T=L kills the intersection.
This extends R172 without adjoining fractional roots of L.

For the bounded retraction, the endpoint graph contributes the original
residue class, and the relative shell has valuation fibre (0,gamma(u)]
of Euler characteristic zero. A graph-compatible decomposition and Euler
Fubini supply the intended vanishing argument. Complete native family
trace/retraction bridges, full matching, bounded witness descent and
the resulting kernel equality remain outstanding. Independent Section 8
truncation and summability issues are not changed by this proposal.

All four orange review pages were rendered and visually inspected;
the final specialization display was simplified and re-rendered.
No main manuscript or Lean source was changed. The 4648-declaration
receipt, source hash and dependency pins remain unchanged and cover the
original scalar-aperture class. No new build or audit was necessary for
this documentation-only investigation. No commit or push was made.


## S6-A5-U — upstream compatibility with Section 4

The author points out that Section 4's P_Gamma is precisely the scalar
ideal corresponding to globally named apertures. The synchronized
proposal must preserve this distinction. The upstream sources checked
include the positive tensor presentation and its coefficient-family
admissibility Lambda_X, actual radius ideals and tensor preimages,
the raw bounded retraction and linked theorem, intrinsic radius
quotients, and the positive-ideal degree-zero proof.

The recommended packaging now explicitly keeps I=(P_Gamma) and approved
R069 indexing unchanged. Introduce J_var separately in Section 7.
B/I remains the old defined algebraic object and B/I -> B/J_var is a
further quotient. Only B/J_var is the proposed repaired VF lifting target.
The intrinsic RV tensor presentation survives literally. The enlarged
quotient's tensor presentation must use the preimage of J_var under the
raw comparison; the old scalar factorwise formula is not asserted.
Intrinsic coefficient-translation and VF lifting kernels are distinct.

For every named gamma>=0, the actual class
Q_gamma=[Ann_gamma,structural s,form 0]+[point,structural 1,form gamma]
-[point,structural 1,form 0] is defined without a named RV endpoint.
For the liftable radii of Section 4, Q_gamma=P_gamma. For
U={rv(a):a^2=T} in degree-zero RES, the quadratic variable-blowup
difference is [U]_0*Q_(1/2): its endpoint (U,u,0) is measured-RV-isomorphic
to (U,1,1/2) by equality of total weights. This mixed RES/Gamma relation
does not supply a globally named half-radius RV point or permit
cancelling [U]. It does not license imposing every rational Q_gamma as
an unconditional scalar kernel relation.

The existing retraction is constructed on B before imposing I by
forgetting volume and applying the ordinary bounded Euler map. Its
construction, RES restriction and old I-vanishing theorem remain valid.
The new obligation is J_var subset ker(E). At manuscript level the
endpoint graph is unmeasured-RV-isomorphic to the original object.
A compatible RES/Gamma normal form of the full graph gives shell
support H={(z,s):z in D,0<s<=gamma(z)}. Every bounded half-open fibre has
Euler characteristic zero; Euler Fubini gives chi(H)=0. This is a
noncircular compatibility proof using Sections 3–4 alone. The complete
native new-family/class bridge is not implemented. The raw retraction
also kills each concrete Q_gamma independently of its scalar indexing.

All proposed generators have positive homogeneous degree, so the
already checked PositiveIdealDegreeZero argument preserves degree zero
once the new graded interface is supplied. Existing comparisons of I
into (P) and (P-1) remain valid; their J_var analogues require separate
proofs. No Section 4 or main manuscript source or Lean proof was changed.
The precise record is `reference/upstream-aperture-compatibility.json`,
with an unapplied mathematical draft in the S6-A5 proposal directory.


## S6-A6 — native upstream compatibility proved; kernel verification continues

The author requests a proof of the Section 4 compatibility lemma, a check
of the revised 7.26, and preservation of the rest of the paper before
applying synchronized changes. No main definition or theorem has been
changed. Section 4's scalar ideal I=(P_Gamma) remains unchanged.

Five new, registered native modules prove the RV compatibility for exact
normalized source/endpoint weights and arbitrary bounded definable
aperture functions, including infinite image. Retaining the full graph
reduces a function to a retained coefficient coordinate. Multiplication
by that coordinate is an actual unmeasured RV isomorphism from the full
positive ray to its deep subray. Scissors therefore kill the relative
half-open annulus in the full ordinary RV ring, before Euler evaluation.
The endpoint and source are unmeasured RV-isomorphic. Consequently the
functional annular ideal lies in the actual bounded-forget kernel and
in the kernel of Section 4's actual bounded evaluation, with the compiled
Section 3 T001 adapter constructed rather than assumed. Its generators
are homogeneous of positive degree; the quotient preserves degree zero.

In the full measured RV ring the exact formula is
  image(relation) = ([W_gamma]-[W]) P,
where W_gamma shifts the base form by the aperture value. The native
functional ideal thus maps into (P). No new HK input is used.

Build: 12578 jobs; audit-variable-aperture-section4-compatibility.log:
PASS 4706 complete public types and transitive axiom records, with only
propext, Classical.choice and Quot.sound. All five modules are registered.
Their scope is native RV compatibility, not strong 6.38 or the VF kernel.

Kernel converse check: paired ordinary exceptions and local translations
are already compiled. A first-zero-event truncation, freezing subsequent
operations only on the retained true-core tags, is the current construction
being investigated. The complete relative-family/head-start and witness
descent bridges remain necessary. No claim that 7.26 is already proved.

The cited Integration in ACVF source has a genuine stronger Lemma 3.18:
atomic-ball injections are RV-linear. Its exact proof is present in the
pinned dependency's IntegrationSection3ACVF/RVLinearity.lean. This provides
the appropriate input for strengthening the local affinity preparation
used by the two-cell proof; a Gamma-linear-to-RV-linear implication is not
assumed. The whole proper bounded two-cell adapter remains to be checked.


## S6-A6-V — auxiliary unary variable primitive and current review PDF

The separate UnaryRelativeApertureData, Map, Geometry, Bounds, Charts,
Fibres and Homeomorphism modules are now all registered, compiled and
audited. They construct an actual original-base definable endpoint map
independent of the changing VF coordinate, rather than requiring one
globally named coefficient. The permitted invariance radius varies with
the retained RV labels and is dominated by that fibre's endpoint value.

Definability, injectivity, exact full core-disc image with inverse source
membership, finite endpoint image (derived from RV-to-VF tameness), VF/RV
double bounds, actual clopen graph fibres, local translation charts,
generic unit total derivative, and a proper covariant homeomorphism are
proved. No old primitive, chain type, main definition or theorem changed.
This is unary support for the proposed first-zero matching, not complete
finite-chain matching or an arbitrary-arity variable VF primitive.

The latest full audit passes at 4776 public declaration types and
transitive axiom records, with propext, Classical.choice and Quot.sound
only. All build and audit sessions are closed. Receipt:
Section6/.scratch/audit-unary-relative-aperture-primitive.log.

The review PDF Section6/output/pdf/section6-compatibility-proof-and-kernel-check.pdf
contains six unchanged manuscript context pages and four orange proof/check
pages. All four new pages were rendered and inspected; two corrected
pages were re-rendered and inspected. The right-panel display request
returned queued. Pages 7-8 give the proved Section 4 compatibility lemma
and measured comparison. Pages 9-10 explicitly retain the unfinished
geometric converse, full witness/head-start descent, proper bounded
two-cell adapter, and native Section 8 trace boundary. The specialization
cancellation and natural-subring intersection are explained, without
claiming the full native trace bridge. The manuscript remains unchanged.


## S6-A6-L — prepared variable steps and live ordinary comparison

The full audit now passes at 4823 complete public types and transitive
axiom records (audit-live-ordinary-relative-unary-support.log), with the
same three standard logical principles. The new registered support
constructs finite auxiliary chains, live/frozen ordinary frames, their
canonical transition, whole-source focus extensions on exactly the live
label locus, exact old VF translations and old labels off the new core,
and the actual new core as a proper bounded RV-pullback. Variable unary
steps preserve full prepared RV-pullbacks and finite RV fibres. Active
focus labels are finite on a prepared unary finite-RV-fibre source,
before any endpoint is chosen.

For every actual definable label-constant endpoint map of nonnegative
relative value on a prepared unary source, withRelativeEndpoint now
constructs all auxiliary aperture data, including named label-dependent
invariance radii. Their names are proved from the full focus Gamma graph;
they are not separate existence premises. No global endpoint is chosen.
The original primitive/chain and main manuscript remain unchanged.

The complete first-zero word assembly, matched source/target outputs,
relative-family witness descent and whole revised 7.26 are still pending.
No full numbered matching or kernel theorem is claimed. The current PDF
retains its earlier 4776-declaration receipt; the later support is recorded
here and in the current verification receipt.
