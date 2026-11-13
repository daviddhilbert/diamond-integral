# Historical progress record

Superseded by the current Section 4 status after the author accepted Section 3 as background.

# Section 4 status

Scope: the whole section, with manuscript review and Lean proof progress
tracked separately. **The full section and its retractions are not complete.**

## Current author instruction

The author explicitly instructs: “take unformalized results in sectrion3
as given for now.” The ordinary and measured T001 presentation interfaces
are now accepted, replaceable Section 3 background inputs. Their local
formal transport is no longer a reason to pause Section 4. The complete
proofs of Propositions 4.7 and 4.15, and normalized-map distinctness, are
proved relative to that authorized background. The independent cell and
localization work continues. Older entries describing the adapter as a
blocking completion condition are superseded by this instruction.

## Approved T001 follow-through

The author approved Section 3's T001 correction on November 12. The approval
was confirmed by reading the `section 3` thread. The approval block is
cleared; older progress entries below describing T001 as awaiting review
are historical.

The author has now approved both Section 4 groups, and their orange
review wrappers have been removed from the main manuscript: **S4-T001-1**, kernel descent for the ordinary and measured
Euler assignments in place of tensor inverses; and **S4-T001-2**, the bounded
retraction obtained from the full graded ordinary bounded-Euler map after
forgetting volume. The bounded product map is retained to compute explicit
tensor images, without a claim of tensor injectivity. The corrected-weight
identity for compensated translations is displayed in Proposition 4.7's
proof. The same identity supports the alternative assignment of Remark 4.8.
No new author question is pending.

The colored five-page review copy is preserved as
`reference/section4-T001-colored-approved.pdf`, with the approval record in
`verification/T001-section4-approval.json`. The current resolved extract
contains printed pages 39–47 in ordinary text color. Three LaTeX passes succeeded without unresolved
references; every extracted page's text equals its full-manuscript page.
The full PDF is now 93 pages after synchronizing the approved T001 proof. The request to open it in the right panel
returned **queued**; visibility is unconfirmed.

The local Lean proofs now construct the actual graded RV Euler maps,
ordinary point/affine normalizations, bounded measured restriction, radius
quotient descent and the whole bounded commuting diagram **relative to
explicit transported T001 presentation hypotheses**. The alternative
Remark 4.8 assignment descends by the same corrected-profile invariance.
`ApprovedT001Presentation.Ordinary` and `.Measured` record only upstream
surjectivity and the reverse coefficient-kernel inclusion. They contain no
Section 4 Euler-descent conclusion and introduce no global axiom.

The upstream audit reports an instantiation at canonical, saturated, small
VF/Gamma-generated Gamma-ground scope. That scope is not silently extended
to our arbitrary real/Gamma base. The concrete upstream-to-local transport
is not instantiated here. All clauses of both numbered retractions now
check relative to that transport input, but neither is marked unconditionally complete.
The approved Section 3 statement and both positive proofs are now
synchronized verbatim into the local manuscript, with the same green author
resolution. The adopted block has 6924 characters, exactly matching the
upstream adoption record; it is preserved in
`reference/T001-approved-upstream.tex`. Its review-only explanatory and
formalization-status notes were not imported. Section 3's Lean sources
remain on its separate executor, so the local formal transport is still
not instantiated.

## Author-approved radius indexing

The accepted **R069** restriction remains applied to both the P_gamma
generators and their ideal: radii are nonnegative and admit an original-base
S-definable RV lift. The historical accepted extract is retained as
`reference/section4-radius-accepted.pdf` (printed pp. 43–44 in that build).
All 19 Section 4 referee items remain resolved. The independently found
S4-U003 homogeneous-positive-degree correction remains applied; it is no
longer the active focused extract. The author's limit of one or two visible
review items and standing authorization for clear corrections are retained.

The original upload remains intact. The broad initial review and the
pre-batching source fragment are historical material in
`reference/deferred-proposals/`, not active requests to the author.
R060's independent paper-level reconstruction is in
`reference/R060-independent-review.md`; the actual varieties and graded
geometric identifications are not formalized by its generic ring calculation.

## Lean implementation

The dated progress entries below preserve the implementation history. Earlier
statements that degree-one point nonvanishing or residue compatibility is
open are superseded by the final milestone recorded below.


The latest fully recorded project/type/axiom audit covers **4430 public
§4 declarations, including 2686 theorem declarations**, across 517 modules.
Only `propext`, `Classical.choice` and `Quot.sound` occur as logical axioms.
The full `DiamondIntegral` entry-point build passes. Full finite-Gamma
balancing and the comparison/evaluation maps on the resulting tensors are
now proved for both concrete presentations. The measured degree-one point is now proved nonzero by the residue trace and finite-field specialization. Both complete numbered retraction statements are proved relative to the explicit approved T001 transport interfaces. Those interfaces are not yet instantiated at the manuscript ground scope, so no unconditional numbered retraction is marked complete.

- `StepFunctions.lean`: actual finite-jump integer-valued functions, finite
  ranges and unique recovery of coefficients using neighbouring gaps.
- `EulerGenerators.lean`, `EulerFunctions.lean`, `EulerDecomposition.lean`:
  both generator algebras, actual function ring carriers, Euler functionals,
  canonical expansions and a proved additive generator principle.
- `EulerPointwise.lean`, `EulerIntervals.lean`, `EulerReflection.lean`:
  actual pointwise products, intervals and reflected functions.
- `EulerConvolution.lean`: the ring product equals the constructed unary
  Euler integral of the actual convolution fibre; associativity and
  commutativity follow without an associativity input.
- `EulerIntervalProducts.lean`: all sign and endpoint cases of Notation
  4.11, including zero, for this actual convolution.
- `EulerBoundedSupport.lean`, `EulerBoundedComparison.lean`: bounded
  support, closure under convolution, equality of the Euler theories on
  bounded functions and the corresponding bounded ring equivalence.
- `EulerBoundedGenerators.lean`, `EulerBoundedQuotient.lean`: actual
  bounded point/interval generation; the indicated ideal is proved to be
  the Euler kernel, and the quotient is isomorphic to ℤ.
- `EulerFiniteCuts.lean`: every function determined by finitely many order
  cuts is constructed in the Euler carrier; finite fibre cuts combine over
  a finite range.
- `GammaDefinableEuler.lean`: every actual finite-range unary function with
  first-order Γ-definable fibres over a specified real/Γ base has such a
  representation. This reuses the checked C-minimal finite-threshold proof,
  not an HK theorem. The native Γ order already is the manuscript's
  valuation order; `Additive` changes only group notation.
- `EulerTruncation.lean`: geometric Euler integration over sufficiently
  large closed symmetric intervals equals bounded Euler integration.
  This is a proved unary stabilization theorem, also for non-Archimedean Γ.
- `EulerOrderTransport.lean`: actual order transport preserving both Euler
  functionals and bounded support.
- `EulerUnaryPushforward.lean`: constructed fibre integration and total
  Euler preservation for finite increasing/decreasing/constant pieces, with
  an evaluation theorem identifying the actual fibres of a compatible map.
  Classification of arbitrary definable maps is a separate step.
- `EulerRationalBranches.lean`: positive-power order isomorphisms, all
  signs of rational-affine branches and constructed Euler pushforward for
  compatible weighted power-law pieces, without a linearity theorem input.
- `ReviewCalculations.lean`: supporting graded/localization calculations;
  no actual retraction follows merely from the generic identities.

The first-order boundary above has now been completed for unary functions:

- `EulerBreakpoints.lean` identifies the canonical coefficient supports
  with failure of local constancy of the actual function.
- `GammaOrderLogic.lean` implements order formulas, interiors, complements
  and finite unions on full proper RV-code preimages over the original base.
- `GammaFunctionProvenance.lean` proves every nonzero canonical coefficient
  threshold definable over that base, using the intrinsic finite breakpoint
  set and the checked finite-order minimum-erasure argument.
- `GammaDefinableFunctions.lean` proves the converse classification and
  closure under finite integer-function operations.
- `GammaGroupNames.lean` proves definability of threshold sums and zero
  through the actual RV-language multiplication graph.
- `GammaDefinableConvolution.lean` proves closure under the actual Euler
  convolution and constructs the original-base function subrings.
- `GammaFunctionRing.lean` gives the bijection with the raw carrier of all
  such finite-range functions in ACVF(0,0), transports the ring structure,
  and identifies pointwise addition, convolution multiplication and p₀.
- `GammaBoundedFunctions.lean` proves bounded generation using only
  original-base definable point and interval thresholds.
- `GammaBoundedQuotient.lean` proves that this restricted generator ideal
  is exactly the Euler kernel and its quotient is ℤ.
- `GammaBoundedComparison.lean` preserves actual functions, their original
  base, convolution and Euler values when changing bounded Euler theories.

The degree-zero and polynomial source are now concrete as well:

- `GammaRelationLogic.lean` proves coordinate-substitution and existential
  closure of arbitrary full Gamma relations over the original base.
- `GammaNamesSubgroup.lean` constructs the actual group of base-definable
  Gamma values, including inverses, and its integer group ring.
- `GammaPointAlgebra.lean` proves the injective point-function group-ring
  homomorphism, recovers coefficients by evaluation and computes its Euler
  augmentation. Its functions are bounded; rays and the line are excluded.
- `GammaFunctionPolynomial.lean` constructs the actual source subring
  Z[Gamma_def] + X FN[X], proves its additive decomposition and verifies
  that ray and line assignments are unavailable in degree zero.

The actual unary set invariant and its bijection theorem are now connected:

- `GammaDefinableMaps.lean`, `GammaBaseExtension.lean` and
  `GammaPowerLawCells.lean` provide first-order power-law graphs and finite
  disjoint cell refinements, keeping auxiliary Gamma names explicit.
- `GammaNamedRoots.lean` proves divisibility of the base-definable Gamma
  group through the actual root graph; it does not assert definable RV lifts.
- `GammaEulerSets.lean` constructs canonical unary set Euler values, proves
  independence of the chosen parameter presentation, scissors, bounded
  comparison and stabilization.
- `GammaUnaryPowerPushforward.lean` and `GammaPowerLawBijections.lean` prove
  actual fibre integration and bijection invariance from a finite power-law
  cover, without a linearity or Euler theorem as input.
- `GammaUnaryBijections.lean` obtains that cover from the already-authorized
  replaceable Gamma-linearity input from [18, proof of Lemma 3.18]. Its
  conclusion retains the original base, ACVF(0,0), and the approved
  nontriviality assumption. The exact input and its limits are recorded in
  `verification/CITED-INPUTS.md` and printed by the axiom audit.

The weighted unary integration stage is also proved:

- `EulerUnaryProjection.lean` proves the weighted projection formula and
  identifies cumulative integration with actual ray convolution.
- `EulerCylindricalStrips.lean` constructs both orders of integration for
  compatible open strips and proves they agree. This is a cell calculation,
  not a general higher-dimensional Fubini theorem.
- `GammaQuantifierLogic.lean` and `GammaFibreCounting.lean` prove finite
  Gamma tuple quantification and bounded counting using full code preimages.
  Witnesses are distinct Gamma values, not distinct RV representatives.
- `EulerPowerLawFibres.lean` proves that a finite power-law cover has only
  finitely many values whose fibres exceed the number of pieces.
- `GammaUnaryDescent.lean` combines that bound with original-base counting
  and definability of finite ordered Gamma sets. Its image function is
  proved definable over the original base, although the power-law
  coefficients used internally need not be named there.
- `GammaWeightedPushforward.lean` proves the actual weighted fibre and
  total-integral identities by a finite level-set decomposition.
- `EulerFibreIntegral.lean` proves uniqueness and linearity from actual
  fibre evaluations; `GammaUnaryPushforwardMap.lean` constructs the
  resulting additive map on original-base definable functions, preserving
  total integration and the identity map.

Uniform unary-fibre families with any finite number of Gamma parameters
are now connected as well:

- `GammaFormulaLogic.lean` provides arbitrary definable relation atoms and
  Gamma quantifiers, all interpreted through full RV-code preimages.
- `GammaFamilySlices.lean` names exactly the actual Gamma parameter tuple
  when constructing an individual fibre.
- `GammaUniformCuts.lean` proves a uniform finite cut bound from genuine
  saturation and explicit smallness of both parts of the original base.
- `EulerCutCellValues.lean` handles empty cells, point cells, bounded
  intervals, rays and the line; the value depends only on the order pattern
  and its occupancy. This also gives a fixed finite range.
- `GammaFamilyEuler.lean`, `GammaFamilyCutLogic.lean` and
  `GammaFamilyIntegration.lean` prove finite range and definability of every
  fibre-Euler level set over the original base. Cut endpoints are
  existentially quantified, not added to that base.

`GammaIntegerFamilies.lean` proves pointwise finite-range integer-family
operations and coordinate substitution in all finite Gamma arities.
`GammaWeightedFamilies.lean` constructs actual weighted fibre functions and
coordinate integration as an additive map. It proves the level-sum formula
and preserves finite range and original-base definability, with explicit
saturation and smallness.

`EulerControlledBreakpoints.lean` proves local constancy away from a cut
tuple and bounds the intrinsic breakpoint set by the number of cuts.
`GammaFamilyBoundary.lean` gives the original-base first-order boundary
relation and a uniform finite cardinal bound. `GammaTupleCounting.lean`
counts distinct actual Gamma values in unary fibres with arbitrary finite
Gamma parameter tuples. `FiniteOrderRanks.lean` proves existence and uniqueness of each ordered
rank. `GammaSortedFibres.lean` constructs the corresponding partial point
maps and proves their original-base graph definability. These provide
canonical ordered boundary functions; they do not yet prove general Fubini.

`GammaFiniteGraphPartition.lean` constructs disjoint actual partial
function graphs covering each uniformly finite relation and applies this
to intrinsic boundaries. `EulerConstantRegions.lean` proves constancy
between breakpoints.

`EulerGerms.lean` identifies left, right and far-left values and recovers
canonical point/ray coefficients from them. `GammaGermLogic.lean` and
`GammaGermFamilies.lean` prove their finite range and original-base
definability. `GammaUniformFiniteFibres.lean` counts actual Gamma fibres
through genuine saturation; `GammaWeightedBoundary.lean` constructs
original-base finite graph partitions for integer-valued family boundaries.
`GammaPartialEvaluation.lean` proves that evaluating a family along one
of these partial graphs and extending by zero preserves the original base.
These support the canonical point-and-ray proof of two-coordinate Fubini
and the parametric coordinate-commutation theorem.

`GammaCanonicalExpansion.lean` identifies every actual weighted fibre
with its finite point-and-ray expansion, carrying original-base coefficient
weights on the boundary graphs. `GammaPartialMaps.lean` totalizes the maps
over that base. `EulerRationalProjection.lean` and
`GammaUnaryProjection.lean` prove weighted projection for arbitrary actual
finite-jump weights under the definable unary maps.

`EulerKernelFubini.lean` constructs actual row and column functions and
proves equality of their total Euler integrals from unary projection data.
`GammaKernelDecomposition.lean` constructs every required datum for an
actual definable function on Gamma squared. `GammaFubiniTwo.lean` therefore
proves two-coordinate weighted Fubini for both Euler characteristics,
retaining ACVF(0,0), saturation, both base-smallness conditions, nontrivial
base Gamma, and the authorized explicit Gamma-linearity input.
`GammaIndicators.lean` supplies actual characteristic functions and scissors;
`GammaIteratedIntegral.lean` constructs integration in a fixed coordinate
order. `GammaFamilySlicesTwo.lean`, `GammaFibreIntegralCongruence.lean`
and `GammaParameterExtension.lean` connect the two-coordinate theorem to
arbitrary finite parameter tuples in `GammaParametricFubini.lean`.
`GammaCoordinatePullback.lean` proves naturality under substitutions in the
remaining coordinates. `FinitePermutationGeneration.lean` and
`GammaFubiniPermutation.lean` prove invariance under every finite coordinate
permutation, for both Euler characteristics.

`FiniteTupleBlocks.lean`, `FiniteTupleRotation.lean` and
`GammaBlockSlices.lean` keep finite prefix and suffix coordinates explicit.
`GammaPrefixIntegration.lean` constructs the original-base additive prefix
integral and proves that its value equals integration over the actual fibre.
`GammaGraphIntegration.lean` computes singleton graph-output integrals.
`GammaUnaryFamilyBridge.lean` connects unary families to the existing
original-base Euler-function subgroup. `GammaHigherPushforward.lean`
constructs the additive weighted pushforward from Gamma^n to Gamma, with
actual fibre evaluations and preservation of the total Euler integral.

`GammaBoundedFamilies.lean` proves that both Euler theories agree on every
finite-dimensional family supported in a bounded box. Each unary fibre is
bounded, and the support of its integral lies in the projected box. The
comparison needs no Gamma-linearity or Fubini input.

`GammaWeightProfiles.lean` constructs the corrected weight μ(x) + Σx
(native Gamma multiplication), proves its original-base definability, and
constructs the actual function-valued profile on a definable Gamma set.
Partial definable weights can be extended by zero in paper notation
(native value one) outside their domain without changing the base.
Descent to the actual graded categories and multiplicativity remain separate.

`GammaBlockFubini.lean` proves Fubini for any two finite coordinate blocks.
`GammaPointFamilies.lean` computes actual finite-dimensional point masses.
`GammaBijectiveRelations.lean` uses singleton and empty graph fibres to
prove invariance under actual definable bijections between Gamma sets in
arbitrary finite arities, including different ambient dimensions.
`GammaIntegralCongruence.lean` proves independence of the parameter-base
presentation of an actual function. `GammaProductFamilies.lean` constructs
actual products, computes their prefix integrals and proves multiplicativity
of total Euler integration. The product calculation needs no Gamma-linearity
or Fubini input.

`GammaMapOrder.lean` proves original-base comparisons, piecewise choices
and maxima. `GammaRadius.lean` constructs a proper definable radius with
sublevel sets exactly equal to the symmetric boxes. `GammaRadiusProfiles.lean`
proves that both Euler theories have the same radius profile because each
radius fibre is bounded, and proves stabilization of its unary truncations.
`GammaHigherProjection.lean` proves the actual weighted projection formula
from Gamma^n to Gamma. `GammaPushforwardCongruence.lean` proves independence
of the base presentation of that actual pushforward.

`GammaSymmetricTruncation.lean` identifies the integral of the actual
symmetric-box restriction with unary truncation of the radius profile.
`GammaBoxStabilization.lean` combines these proved identities to establish
stabilization in every finite dimension. The radius is arbitrary and named
only in an explicit finite Gamma base extension. Its stabilized value is
the bounded integral over the original base. No Archimedean assumption or
HK input is used.

`GammaProfileBijections.lean` proves actual function-valued profile
invariance under a definable bijection preserving the Gamma target map.
`GammaMeasuredProfileInvariance.lean` derives this condition from the
manuscript's Gamma-Jacobian volume equation. `GammaConstantPushforward.lean`
computes pushforward under an actual constant corrected weight.
`GammaCounterweightedRay.lean` consequently computes the actual Gamma-side
profile of ((0,infinity),-id): -p_0 for geometric Euler and zero for bounded
Euler. This supports the corrected +[1] target calculation, but the RES
assignment and complete retraction are still separate obligations.
`GammaPushforwardSupport.lean` proves that output support lies in the
image of the nonzero source support. `GammaBoundedProfiles.lean` proves
bounded support from explicit bounds on the source and volume form, and
proves that both actual profiles agree whenever the source is bounded.
`GammaBoundedMapImage.lean` supplies the actual volume bound from the
proved 2.41 theorem through full raw RV-code graphs. Its canonical-structure
premise is explicit. `GammaBoundedProfileRange.lean` then constructs the
bounded-ring-valued profile, proves its Euler value is the source integral,
and identifies the profiles for the two Euler theories.

`GammaProfileScissors.lean` proves scissors for the actual function-valued
profiles. `GammaProfileRestrictions.lean` proves independence from the
chosen global extension of a partial volume form and constructs partial
profiles over the original base.

`GammaZeroDegreeProfile.lean` computes each actual zero-arity profile as
an integer point mass and proves that its Gamma value is definable over
the original base. The profile belongs to the proved point group-ring
subring, supplying the degree-zero coefficient restriction.
`GammaObjectPolynomial.lean` constructs the actual homogeneous object
assignment in Z[Gamma_def] + X FN[X] and proves its coefficient formula.
The assignment descends to the explicit chart quotient below; its
identification with the manuscript category remains separate.

`GammaReflectedFamilies.lean` constructs actual reflected unary families.
`GammaSumMap.lean` checks the product-volume and corrected-weight identity
on explicit coordinate blocks. `GammaSumFibres.lean` computes the actual
inner integral in each sum fibre. `GammaPushforwardConvolution.lean` combines
that calculation with the proved projection formula and Fubini to identify
pushforward under a sum with actual Euler convolution of the two profiles.
`GammaProfileProducts.lean` proves multiplicativity of the actual corrected
profiles on products of definable Gamma sets, using the checked coordinate
product and sum-weight formulas. `GammaObjectMultiplication.lean` proves
that the actual homogeneous polynomial assignment preserves products and
the degree-zero unit, including its point-group-ring coefficient.
`GammaObjectRelations.lean` proves that the polynomial assignment respects
volume-preserving definable bijections, scissors, empty domains and weight
restriction. Descent to the auxiliary chart quotient is proved below; descent from
the actual manuscript category still needs its explicit presentation.

`GammaCellSections.lean` and `GammaCellUnboundedSections.lean` compute
graph, open-band, ray and line sections from the actual point and interval
Euler functions. `GammaCylindricalCells.lean` proves the geometric value
(-1)^d for recursive cylindrical graph/interval witnesses. This does not
prove existence of classical o-minimal cell decompositions or identify a
separate topological dimension definition. `GammaFinitePartitions.lean`
proves additivity on actual finite disjoint partitions.
`GammaCellFormula.lean` proves the sum of (-1)^d for every supplied finite
cylindrical cell decomposition.

`GammaWeightedCharts.lean` stores actual Gamma domains and volume forms
whose full graphs are definable only on those domains.
`GammaChartOperations.lean` constructs actual product charts and the
zero-degree unit and checks their polynomial values.
`GammaChartPresentation.lean` constructs a concrete ring quotient by
product, unit, empty, scissors and volume-preserving definable-bijection
relations, then constructs both ring homomorphisms to the restricted
polynomial ring. This auxiliary presentation uses all such definable
bijections. It is not identified here with the manuscript category, whose
Gamma morphisms have an additional RV-lift condition.

`GammaBoundedPolynomial.lean` constructs the actual bounded restricted
polynomial source and its injective map into the unbounded source.
`GammaBoundedObjectPolynomial.lean` constructs each bounded object's value
and proves coefficientwise Euler evaluation gives chi(I) X^n.
`GammaBoundedSpecialization.lean` constructs the actual source-ring
specialization to any commutative ring at T and proves the assignments
p_gamma X^n -> T^n and o_gamma X^n -> -T^n, as well as chi(I) T^n for actual
bounded objects. The source and volume bounds use the proved 2.41 bridge,
with its canonical-structure premise explicit.
`GammaBoundedProducts.lean` proves closure of actual box-bounded domains
under subsets, finite unions and coordinate-block products.

`EulerEndpointProjection.lean` constructs the actual endpoint ring
projection p_a -> p_a, q_a -> -p_a, line -> 0.
`GammaEndpointProjection.lean` proves that its image lies in the original-base
point group ring. `GammaUnboundedSpecialization.lean` and
`GammaUnboundedAssignments.lean` construct the source specialization for any
character of the definable Gamma group and prove the paper's positive-degree
point/ray/line assignments, including the +point geometric sign for the
counterweighted ray after T+Q=0. No actual RES ring is supplied by that calculation.
`GammaChartSpecializations.lean` composes this map with the constructed
chart quotient homomorphism and evaluates the actual counterweighted ray class.

`GammaBoundedChartMap.lean` constructs the bounded-source homomorphism
on the subring generated by actual bounded charts, using the proved 2.41
bridge and the injectivity of the bounded polynomial inclusion.
`GammaBoundedChartComparison.lean` proves that the resulting specialization
is independent of the Euler choice on that entire subring.
`GammaSpecializationComparison.lean` proves that the unbounded specialization
with the trivial volume character restricts to the bounded specialization,
both on the actual polynomial source and on the bounded chart subring.

`GammaRVLifts.lean` defines the actual original-base definable RV units and
their value subgroup. Its inclusion in the definable Gamma group is proved;
no divisibility or definable section is asserted for the liftable subgroup.
The accepted nonnegative-radius indexing is implemented as the nonnegative
part of this subgroup and is characterized by an original-base definable
RV point. This does not construct P_gamma in an RV Grothendieck ring.
`GammaRadiusAnnulus.lean` computes the actual half-open Gamma annulus
(0,gamma] as a difference of two rays. Its integral and its constructed
bounded chart specialization are zero for every admissible radius,
including the separate empty set at radius zero.

`GammaRVChartPresentation.lean` now retains the manuscript's RV-contraction
restriction explicitly: each allowed chart isomorphism carries a definable
bijection between the full proper RV preimages over the original base,
and a proved contraction equation. Its relation ideal maps into the
all-bijections ideal, so both constructed profile homomorphisms descend
to this restricted presentation. Identification with finite tagged unions
and the actual graded category is still open; the restriction itself is
no longer absent from the formal objects.

`RVMeasuredCharts.lean` begins the actual measured RV and RES object layer.
Coordinate maps have proper RV outputs and finite fibres; partial volume
forms and isomorphism graphs are definable over the original base. The
corrected-weight equation is proved equivalent to the manuscript volume
formula. RES objects retain finite full value patterns, including infinity.
Every degree-zero RV domain is proved finite and hence gives a RES object;
this does not split a finite RV set into definable singleton points.
All definable Gamma values give actual degree-zero weighted RES units,
without requiring RV lifts of their volume weights.
`RVPointChoices.lean` constructs actual measured RES singleton objects and
an original-base definable isomorphism between any two definable RV lifts
of the same radius with constant zero volume. This establishes the point
choice calculation before passage to an RV Grothendieck ring.

`RVSharpCharts.lean` constructs the actual full RV preimage of each
weighted Gamma chart, preserving the original base and partial volume
form. Actual RV-induced Gamma isomorphisms give measured RV isomorphisms;
the lift graph and the corrected-weight equation are proved. This is an
object/isomorphism bridge, not a product/tensor descent theorem.

`GammaTupleMaps.lean` proves original-base definability of tuple-map
graphs, images, preimages and scalar compositions from the actual coordinate
graphs. `GammaTranslation.lean` proves numerical translation invariance for
both Euler characteristics in every finite dimension. The translated target
volume is constructed and proved definable, with its compensation and
actual profile equality checked. Translation constants need only be
Gamma-definable; no original-base RV lift is assumed by these identities.
These are the Gamma calculations relevant to the latest §3 kernel report,
not a proof of its geometric kernel-generation or global tensor descent.

`RVMeasuredGroup.lean` constructs the fixed-degree additive scissors
presentation on actual measured RV charts. It imposes actual definable
volume-preserving isomorphisms, empty objects and the weighted scissors
relations, and proves its additive universal property including uniqueness.
`RVRadiusGenerators.lean` constructs the actual P_gamma additive classes
for precisely the accepted radii. The lift choice is proved independent,
a canonical indexed class is defined, and the zero-radius class is proved
zero using the empty annulus and actual singleton isomorphism.
`RVMeasuredBounds.lean` proves that all actual RES chart domains are doubly
bounded from their finite full value-pattern range, without Archimedean or
definable-choice assumptions. `RVRadiusBounds.lean` proves that each actual radius-generator chart is
doubly bounded and that its class belongs to the additive span of bounded
chart classes in the ambient scissors group. This is not asserted to be
an injective bounded-category presentation. These steps do not yet construct
the graded product ring, P_Gamma ideal or a retraction on those RV classes.

`FiniteTupleGraphProduct.lean` and `RVRealProducts.lean` prove the actual
coordinate rearrangement and original-base definability of products of
partial RV map graphs. `RVVolumeMaps.lean` proves multiplication and
coordinate restriction of partial Gamma volume forms using full RV-code
fibres and projection, without choosing representatives over the base.
`RVMeasuredProduct.lean` constructs the actual RV product object, including
its finite coordinate fibres and partial volume graph.
`RVMeasuredProductProperties.lean` proves corrected-weight multiplicativity,
finite RES value-pattern closure and preservation of doubly bounded domains.
These are actual object operations; the graded Grothendieck rings and their
RES/RV tensor descent remain unfinished.

`RESChartRing.lean` constructs a concrete ring quotient on actual measured
RES charts, with actual product, unit, isomorphism, empty and scissors
relations and its proved universal map. A grading and identification with
the finite-coproduct category presentation are not asserted by that definition.
`RESWeightCharacter.lean` realizes the definable-Gamma weight character
by actual degree-zero RES units; its multiplicativity follows from an
actual measured RV product isomorphism. `RVCoordinateMaps.lean` constructs
original-base coordinate graphs and their measured isomorphisms.
`RVWeightScaling.lean` proves that multiplication by a degree-zero weighted
RES unit scales every actual partial volume form, including the equality
of their classes in the concrete RES ring.
`RESFibreObjects.lean` constructs actual measured value-fibre RES objects,
the torus and the degree-one point. Finite Gamma support is proved to give
finite full RV value patterns; no RV lift of a definable value is assumed.

`RESMeasuredReduction.lean` constructs the concrete measured RES chart
quotient by the actual value-fibre relations and the degree-one affine-line
class. `RESUnboundedPsi.lean` constructs ψ from the actual restricted
polynomial source into that quotient. Its assignments are proved using
actual weighted torus/point objects and the zero-degree weight character;
the counterweighted geometric ray evaluates to the degree-one point class
and the bounded value is zero. This is not yet a map from the full RV ring,
a proof of nonzero point class, a grading or the category identification.
`GammaSingletonProfiles.lean` computes the actual profile and homogeneous
polynomial of a weighted Gamma singleton, without an RV lift of either
Gamma value. It retains the characteristic, saturation and base-smallness
hypotheses of the actual profile construction.

`RESFiniteBalancing.lean` identifies the computed weighted Gamma singleton
profile, after ψ, with the actual measured RES value-fibre class. This is a
proved degree-one balancing calculation using exactly the constructed
fibre ideal; neither Gamma value needs a definable RV lift. Full finite-Gamma
balancing and global tensor descent are separate obligations.

`RVForgetScissors.lean` proves that forgetting corrected weight preserves
scissors, using injectivity on the packed graph of the union object.
`RESOrdinaryRing.lean` constructs the ordinary RES chart ring and the actual
forgetful ring map; its volume labels are redundant, and all zero-degree
volume weights map to the unit. No finite RV coefficient is split into points.
`RESOrdinaryReduction.lean` constructs the ordinary value-fibre quotient,
proves the measured fibre ideal vanishes under forgetting and retains the
affine-line class in this target.
`RESBoundedPsi.lean` constructs bounded ψ into that concrete ordinary RES
quotient, with point/interval assignments, the χ(I)[G_m]^n formula on actual
bounded charts and independence of the Euler choice on the full generated
chart subring. `GammaBoundedSingletonProfiles.lean` identifies the actual
bounded singleton polynomial through the proved injective bounded inclusion.
`RESBoundedFiniteBalancing.lean` then proves its image agrees with the
forgetful class of the actual measured RES fibre. This is degree-one
balancing, not a global RV descent or a grading/category identification.

`PolynomialDiagonal.lean` and `PolynomialCoactionGrading.lean` prove the
coefficient reconstruction and uniqueness needed for an actual natural-number
grading. `RESRingCoaction.lean` and `RESGrading.lean` apply this to the measured
RES chart ring, with finite homogeneous decomposition and a `GradedRing`
instance. `RESOrdinaryUniversal.lean` gives the ordinary presentation's
universal property; `RESOrdinaryGrading.lean` constructs its grading and
proves that forgetting volume commutes with homogeneous components.
`PolynomialCoactionQuotient.lean` proves descent through homogeneous ideals.
`RESReductionGradings.lean` proves homogeneity of the actual value-fibre
ideals and measured affine-line ideal and constructs the gradings of both
actual quotient targets. These are gradings of the concrete chart rings;
the finite-coproduct category comparison, graded source maps and global RV
descent remain separate obligations.

`RestrictedPolynomialGrading.lean` proves the natural grading with a
restricted constant-coefficient subring. `GammaPolynomialGradings.lean`
constructs full gradings on both actual Gamma polynomial sources, proves
the bounded inclusion preserves degree and puts actual object polynomials
in their stated homogeneous pieces. `RESPsiGradings.lean` proves both psi
maps preserve degree on every homogeneous source element and bundles them
as graded ring homomorphisms. `RVChartRing.lean` constructs the ring
presentation on all actual measured RV charts; its finite-coproduct
category identification and tensor descent remain open.

`RVGrading.lean` gives the concrete full measured RV ring its actual
natural-number grading. `RVChartMaps.lean` maps the fixed-degree additive
scissors groups and measured RES ring into it and proves degree preservation;
no injectivity of these maps is asserted. `RVBoundedCharts.lean` constructs
bounded objects, their unit and products and the actual bounded RES
inclusion. `RVBoundedRing.lean` and `RVBoundedGrading.lean` construct the
ring presentation on bounded objects themselves and its full grading.

`RVBoundedMaps.lean` constructs degree-preserving maps from measured RES
to the bounded RV ring and from there to the full RV ring, and proves their
composite is the earlier RES inclusion. `RESOrdinaryPoints.lean` proves
ordinary singleton cancellation for any two original-base definable proper
RV points, without requiring their values equal. `RVRadiusIdeal.lean`
constructs the actual P_gamma classes in the bounded ring, with proved lift
independence, zero-radius vanishing and degree one. Their ideal is proved
homogeneous and their full-RV images agree with the earlier additive
classes. `RVRadiusQuotient.lean` constructs the actual graded quotient by
that ideal, including the degree-preserving RES map. This is not a proof
that a global retraction kills the ideal: that retraction remains open.

`RVSharpProducts.lean` proves actual original-base measured RV product
and unit isomorphisms for full proper Gamma preimages. `RVSharpScissors.lean`
proves preservation of weighted scissors and empty charts.
`RVSharpRingMap.lean` descends this construction from the actual
RV-contraction-restricted Gamma presentation to the full measured RV ring.
`GammaRVUniversal.lean` supplies the source universal property and
`GammaRVGrading.lean` its full grading. `GammaRVMapGradings.lean` proves
and bundles degree preservation of sharp, both actual Gamma polynomial
profile homomorphisms and their composites with measured psi. This supplies
the actual graded right-factor evaluations, without assuming a tensor
isomorphism or the global RV retractions.

`GammaBoundedRVCharts.lean` and `GammaBoundedRVPresentation.lean`
construct intrinsic bounded Gamma objects and their ring with actual
RV-contraction lifts; they are not identified with a subring of the
unbounded presentation. `GammaBoundedRVMaps.lean` constructs the bounded
sharp map, the bounded-to-unbounded map and a proved map to the auxiliary
bounded chart subring. The sharp comparison square commutes.
`GammaBoundedRVGrading.lean` proves the full grading and
`GammaBoundedRVProfiles.lean` constructs the graded bounded profile and
ordinary RES evaluation. This evaluation is independent of Euler choice
on the entire intrinsic bounded Gamma presentation, retaining the explicit
canonical-structure, characteristic, linearity, saturation, smallness and
nontriviality hypotheses of the bounded profile bridge.

`RVBoundedTensor.lean` constructs actual product comparison and evaluation
maps on the tensor product over integers, with Euler-choice independence.
`RVRadiusTensor.lean` gives an explicit preimage of every accepted P_gamma
under that comparison and proves its constructed evaluation is zero using
the actual annulus and ordinary singleton calculations. These are the
earlier integer-tensor maps. The finite-Gamma-balanced maps are now proved
below; global RV descent does not follow just from these computations.

`GammaUnaryIdentityProfile.lean` proves that unary corrected-weight
pushforward with constant zero volume is the actual indicator function;
the positive ray has profile q_0 for both Euler theories.
`RVMeasuredTensor.lean` constructs the integer-tensor comparison and
measured evaluation on the actual unbounded rings.
`RVMeasuredSpecialClasses.lean` constructs actual degree-one P and h
classes with explicit preimages. The P preimage evaluates to zero for
both Euler choices; the h preimage evaluates to the degree-one point
geometrically and zero for bounded Euler. These are proved preimage
computations. Neither global RV descent nor nonzero point class follows
from them, and Proposition 4.7 remains incomplete.

`GammaFiniteNames.lean` proves that every coordinate and partial weight
of a finite definable Gamma chart is definable over the original base.
`GammaTupleSingletonProfiles.lean` computes weighted singleton profiles and
polynomials in every finite arity, including degree zero.
`GammaFiniteBounds.lean` proves every finite Gamma domain doubly bounded.
`GammaRVIdentityIso.lean` constructs actual RV-lifted identity isomorphisms
for equal domains and partial weights, including normalized extensions.
`GammaNameTuples.lean` indexes every finite definable Gamma domain by a
finite set of original-base Gamma-name tuples, with no RV representatives.
These supply the finite-Gamma generation used by the full balancing proofs
below; global tensor-kernel descent remains open.

`GammaFiniteRVCharts.lean` and `GammaFiniteRVPresentation.lean`
construct intrinsic finite Gamma objects and their ring, retaining actual
RV-contraction lifts. Their sharp objects are full RES fibres.
`GammaFiniteRVGrading.lean` proves the full grading.
`GammaFiniteRVMaps.lean` constructs actual maps to RES, bounded Gamma and
full Gamma rings and proves the product comparison squares commute.
`GammaFiniteDecomposition.lean` proves, inside the intrinsic finite ring,
that every finite chart class is a finite sum of original-base named
singleton classes with constant weights. This splits finite Gamma sets;
it does not split finite RV sets into definable points. Full finite-Gamma
balancing is proved below; global tensor-kernel descent remains unfinished.

`GammaFiniteGenerators.lean` proves that ring homomorphisms on the
intrinsic finite-Gamma ring are determined by degree-zero weighted units
and degree-one value fibres, using actual singleton product isomorphisms.
`GammaFiniteRVMapGradings.lean` bundles all coefficient maps as graded.
`RESFiniteUnitBalancing.lean` proves the degree-zero balancing for every
definable Gamma weight. `RESAllFiniteBalancing.lean` and
`RESAllBoundedFiniteBalancing.lean` prove full measured and ordinary bounded
balancing as ring-homomorphism equalities on the entire intrinsic
finite-Gamma ring. `FiniteGammaAlgebras.lean` supplies the actual algebra
structures for forming tensors over that base. Full balancing is now
proved for these presentations; their manuscript category identification,
global RV kernel/descent remain separate obligations.

`RVFiniteBalancedTensor.lean` and `RVBoundedBalancedTensor.lean`
construct actual tensors over the intrinsic finite-Gamma ring, their product
comparison and evaluation maps, and the proved RES-factor restrictions.
The bounded evaluation is independent of Euler choice. Canonical maps from
the earlier integer tensors commute with comparison and evaluation; their
integer algebra instances are made explicit to keep scalar actions aligned.
`RVBalancedSpecialClasses.lean` transfers the actual P, h and admissible
radius preimages and their computed values to these finite-Gamma-balanced
tensors. The tensor gradings and the degree preservation of comparison/evaluation are now proved; global RV kernel/descent remains separate.

`TensorPolynomialCoaction.lean` and `TensorCoactionGrading.lean` prove
full gradings for tensors over graded coefficient rings using finite
homogeneous decompositions. `TensorGradedMaps.lean` supplies the whole-tensor
map criterion. `RVBalancedGradings.lean` and `RVBalancedMapGradings.lean`
apply these proofs to both actual finite-Gamma-balanced sources and their
comparison/evaluation maps. `RVBalancedSpecialGradings.lean` proves P, h and
all accepted radius preimages have degree one.
`RVBalancedRadiusIdeal.lean` proves their tensor radius ideal homogeneous,
its comparison image exactly the bounded RV radius ideal, and its vanishing
under bounded evaluation. `CoactionGradedMaps.lean` constructs graded lifts
through homogeneous quotients. `RVBalancedRadiusQuotient.lean` constructs
the graded tensor quotient, its actual comparison/evaluation maps, the RES
restriction and independence of Euler choice. These source-quotient maps
do not assert descent through the full RV comparison kernel.

`GammaTranslationCharts.lean` constructs actual compensated translations
of partial-volume charts; `GammaBoundedTranslationCharts.lean` proves they
preserve double bounds, with no RV-lift or Archimedean assumption.
`RVVolumeIsoEvaluation.lean` proves both tensor evaluations identify
Gamma volume-isomorphic charts. `RVTranslationEvaluation.lean` and
`RVTranslationIdeals.lean` prove actual translation differences and their
homogeneous ideals vanish under evaluation. These are evaluation ideals,
not a proved presentation of the RV comparison kernels.
`RVZeroDegreeRES.lean` proves surjectivity of RES onto each degree-zero RV
piece. `RVZeroDegreeRetraction.lean` constructs explicit inverse maps there,
and `RVZeroDegreeEquivalences.lean` packages both ring equivalences. These
proofs retain finite RV domains without splitting them into named points.

`PositiveIdealDegreeZero.lean` proves that a homogeneous quotient whose
ideal vanishes under zero-degree projection preserves the zero-degree
subring. `ReductionDegreeZero.lean` applies it to the measured RES quotient,
ordinary RES fibre quotient and accepted bounded RV radius quotient,
constructing all three degree-zero ring equivalences. Thus the radius
restriction does not remove arbitrary degree-zero Gamma weights.

`RVFiniteWeightedCounts.lean` constructs finite weighted counts in the
full Gamma group ring and proves isomorphism/scissor invariance and product
multiplicativity. `RVZeroWeightedCount.lean` gives the resulting ring
invariant, zero on positive grades. `RESWeightEmbedding.lean` proves the
entire definable-Gamma weight group ring embeds in measured RES and remains
injective in both the measured RES quotient and accepted bounded RV radius
quotient. It agrees with the character used by psi. The measured target is
therefore nontrivial; the degree-one point's nonvanishing remains open.
No finite RV set is split into definable singleton objects.

`GammaBoundedRVEmpty.lean` proves every empty-support bounded Gamma
chart has zero class independently of volume extensions.
`RVBalancedRadiusChoices.lean` proves lift independence of the actual tensor
radius preimage and its zero-radius vanishing already in the source tensor.
`RVBalancedRadiusDegreeZero.lean` proves the tensor radius quotient preserves
its entire degree-zero subring; the actual RES map is injective on degree
zero and the full definable-Gamma weight ring embeds there. This also proves
the tensor radius quotient is nontrivial without global tensor injectivity.

`GammaZeroDegreeFinite.lean` gives explicit inverses to both intrinsic
finite-Gamma coefficient maps in degree zero. `TensorZeroDegree.lean`
proves zero-degree tensors come from the left factor whenever right
zero-degree elements come from zero-degree coefficients.
`RVBalancedZeroDegree.lean` proves the actual RES factor is the entire
zero-degree subring in both balanced tensor sources and their radius
quotient. All three actual comparison maps are injective on degree zero.
The remaining global comparison-kernel obstruction is in positive degree.

`CoactionKernel.lean` proves coaction-compatible ring-map kernels are
homogeneous, and injectivity in degree zero gives a finite decomposition
into positive-degree homogeneous kernel elements. `RVComparisonKernels.lean`
applies this to the actual measured, bounded and radius-quotient comparison
maps. This reduces the global kernel problem by degree; its generators and
evaluation descent through the whole kernel remain open.

`RVUnderlyingIsomorphisms.lean` constructs actual original-base
underlying RV bijections between charts of different degrees, including
inverses. `RVUnderlyingProducts.lean` proves Cartesian products retain
definable graphs. `RESPointTuples.lean` constructs point objects in every
grade and computes their ordinary classes as powers of the degree-one
point; `RESPointIdentification.lean` identifies it with the manuscript's
point object. `RESHomogenization.lean` proves the actual point-factor
identity for every cross-degree underlying RES bijection.
`RESDimensionFreeRing.lean` constructs the corresponding dimension-free
chart presentation and proves its forget-degree kernel exactly ([1]-1).
`RESDimensionFreeReduction.lean` proves compatibility with the ordinary
value-fibre quotient, with explicit normalization equivalence and kernel.
The actual point-localization comparison is now proved below. Finite-coproduct
category identification remains separate; no full numbered retraction is inferred.

`PointLocalizationNormalization.lean` constructs normalization by evaluating
the grading coaction at the inverse of a degree-one point, and proves its
image is the actual homogeneous degree-zero localization.
`PointLocalizationEquivalence.lean` constructs inverse ring maps proving
R/(q-1) is that localization, without a nonzerodivisor hypothesis.
`RESPointLocalization.lean` applies this to the concrete ordinary RES fibre
quotient and dimension-free chart presentation, with the proved formula
[U]/[1]^k for every degree-k chart and point fraction equal to one. These
are actual localization maps; finite-coproduct category identification and
global RV descent remain separate. Named local grading helpers are included
in the full type/axiom audit.

`GammaEulerEvaluation.lean` constructs both ordinary Gamma evaluations
using the actual total Euler character, with the chi(I) T^n formula.
`GammaOrdinaryEvaluation.lean` proves grading and full finite-Gamma
balancing on unbounded sources without a canonical-structure premise.
`RVOrdinaryTensorEvaluation.lean` constructs the resulting ordinary maps
on the actual full balanced tensor. `GammaOrdinarySpecialClasses.lean`
and `RVOrdinarySpecialValues.lean` prove the actual ray, P and h values in
the ordinary target, which retains the affine-line class.
`GammaEulerPolynomialMaps.lean` proves target naturality and positive-degree
vanishing at T=0. `RVOrdinaryDimensionFreeEvaluation.lean` constructs both
ordinary dimension-free tensor maps, proves their P-1 relations, and proves
geometric vanishing for every homogeneous positive-degree Gamma element
after imposing affine-line class one. This is the actual tensor version of
S4-U003; global RV descent and the complete retractions remain open.

`GammaOrdinaryBoundedComparison.lean` proves compatibility of the full
ordinary Gamma evaluation with the earlier bounded profile map.
`RVBoundedTensorComparison.lean` constructs the actual graded bounded-to-full
tensor map and proves its RV comparison and evaluation squares commute.
`GammaEulerBoundedComparison.lean` proves Euler-choice independence directly
from bounded Euler comparison, without a canonical-structure premise.
`RVBoundedOrdinaryEvaluation.lean` and `RVBoundedOrdinaryRadius.lean`
construct the direct bounded evaluation and graded radius-quotient descent,
prove RES restriction and Euler-choice independence, and prove agreement
with the earlier constructions when their canonical-structure premise is
available. All accepted radius relations vanish, including radius zero.
This removes that premise from these tensor maps, not from all remaining
RV/category arguments.
`RESAffineLocalization.lean` constructs the actual natural affine-localized
comparison and proves its homogeneous fraction formula. No injectivity is
assumed. The separate actual point-localized isomorphism remains proved.
The geometric zero-divisor counterexample in R060 remains paper-level.

Remaining work includes identification with the classical cell-dimension
convention, identification with the finite-coproduct manuscript categories, actual tensor/kernel descent, and both complete
retractions. The separate §3 chat now reports a finite-coefficient obstruction to
tensor injectivity under the current ground-parameter conventions (T001,
awaiting author review there). Its follow-up source audit reports that the
fixed-ground issue persists in the examined HK versions; multiplying the
proposed tensor pair by the degree-one Gamma point coefficient kills that
particular difference. Under the tensor comparison, that Gamma point is
the RES torus class [G_m], so this is torus localization; it is not the
RES degree-one point [1] used in the bounded normalization. The latest
upstream paper-level kernel presentation also reports a torus annihilator
for the whole kernel. None of these statements is an imported Lean kernel
theorem or a proof of the unlocalized tensor isomorphism here. Its reported example uses the finite RV set
of fifth roots of rv(t) and rays translated by val(t)/5. That report is not
a Lean theorem imported here, and the local checkout still contains only
its README. The latest §3 follow-up gives a paper-level kernel-generation argument
and reports that both unmeasured Euler evaluations annihilate it directly,
because the generators compare Gamma translates. It proposes descent
through the proved surjection in place of an inverse, with no further RES
quotient. The measured follow-up uses compensated target volume forms. The latest
upstream update reports a first Lean verification of elementary positive
relations and a surjective quotient map, with the reverse kernel inclusion
still open; these exports are not present in this checkout.
Those complete kernel/descent statements are not Lean exports here and
the §3 colored proposal remains unincorporated in this checkout.
The actual §4 RES/RV descent must be checked against that kernel
presentation; tensor injectivity is not assumed in these Γ proofs.
The independent Gamma integration proofs do not assume the tensor
isomorphism. No unpublished §3 interface is assumed here. No HK theorem is an input.
Bibliography items 18–22 retain their authorized replaceable-input policy.

## Environment and verification

The prepared workspace lacked the existing author-approved finite-open-radius
patch in the pinned companion library. Running `section 2/prepare-reuse.py`
restored its exact 30-file, checksum-verified patch. The subsequent full
project entry-point build passed. The verifier now prepares that patch
idempotently before builds and records its manifest and patch identity.

Run `python3 'section 4/verify.py'` in the activated pinned Lean environment.
It builds `DiamondIntegral` and prints complete types and axioms of every
listed §4 export. Export counts are not complete numbered-result counts.
The current numbered-result inventory is `COVERAGE.md`.

`build-review.py` rebuilds the full manuscript and extracts at most two
items using stable LaTeX labels; the current invocation is:

```
python3 'section 4/build-review.py' --start-label review:section4:T001:start --end-label review:section4:T001:end --items S4-T001-1 S4-T001-2 --colored-pages-only
```

No commit or push is authorized in this chat. Preserve all local work.


The accepted radius restriction now has its actual forgetful-map proofs.
`RVOrdinaryRing.lean` and `RVOrdinaryGrading.lean` construct the ordinary RV
chart ring and its full grading. `RVOrdinaryMaps.lean` constructs its RES
inclusion and measured forgetful maps, with their commuting square.
`RVNamedMultiplication.lean` eliminates a temporary RV point name to prove
the scaling graph definable over the original base; `RVScaledRays.lean`
constructs the explicit ray bijection and inverse. `RVOrdinaryRadius.lean`
uses actual scissors to prove that every accepted Pγ has zero ordinary RV
image, including radius zero, and constructs the forgetful map from the
actual bounded radius quotient. `RVOrdinaryMapGradings.lean` proves that
these maps preserve degree. `RVMeasuredScaling.lean` retains the volume
weight in the same scaling construction; `RVMeasuredRadius.lean` proves
that the full measured image is exactly (wγ−1)P. Hence both forgetful ideal
inclusions in Notation 4.13 are proved on the actual chart presentations.
These results do not supply global Euler descent or the finite-coproduct
category identification, and do not complete either numbered proposition.

`RVMeasuredPQuotient.lean` constructs the actual full measured quotient by
P, its full grading and the graded map from the bounded radius quotient.
`RVOrdinaryPNormalization.lean` constructs ordinary RV/(P−1) and the other
natural map from the bounded radius quotient. Both maps commute with
their RES inclusions. `RVMeasuredPDegreeZero.lean` proves that the measured
P quotient preserves every degree-zero coefficient, that the bounded-to-
full comparison is an isomorphism on its whole degree-zero subrings, and
that the entire definable-Gamma weight ring embeds. In particular this
measured quotient has 0≠1. This does not prove nonvanishing of its degree-one
point or establish a comparison between the two different P quotients.

`RVOrdinaryDegreeZero.lean` constructs the inverse to ordinary RES inclusion
on the full degree-zero subrings, using finite domains without choosing
points. Its projection commutes with forgetting volume from the measured
RV and RES presentations. The current main-PDF display request remains
queued; no visible-panel confirmation has been returned.

The alternative construction in Remark 4.8 has its own actual enlarged
quotient, `RESAlternativeReduction.lean`: weighted degree-one points are
identified, the new ideal is homogeneous, and degree-zero weights are
preserved. `RingHomGluing.lean` proves the algebraic gluing lemma used by
`GammaAlternativeSpecialization.lean` to retain the constant volume
character and use Euler evaluation in positive degree.
`RESAlternativePsi.lean` proves all point/ray/line assignments and the full
grading of this alternative geometric psi. `RESAlternativeForget.lean`
constructs the actual ordinary affine-line quotient and the graded
forgetful map from the enlarged measured target. Global RV descent for
this alternative is still open. `GammaAlternativeEvaluation.lean` now proves
its full finite-Gamma balancing, including weighted units and every finite
arity. `RVAlternativeTensorEvaluation.lean` constructs the resulting graded
map on the actual balanced tensor, with its RES restriction, zero value on
the P preimage and +[1] value on h. `GammaAlternativeMaps.lean` proves that
forgetting the volume character turns the alternative polynomial map
into ordinary Euler evaluation.

`RESAlternativeCompatibility.lean` proves that the alternative enlarged
construction commutes with the ordinary geometric Euler evaluation after
forgetting volume and imposing the affine-line relation. This is an
identity on the whole actual finite-Gamma-balanced tensor, including all
zero-degree coefficients, rather than only the P and h computations.

`RESAlternativeRawQuotient.lean` identifies the enlarged target exactly
with the raw measured RES quotient by the old fibre/affine relations and
the actual weighted-point differences. It gives the ring equivalence and
proves the precise kernel of the raw map, matching J+([A]) in the text.

`RESAffineNormalization.lean` constructs the actual degree-normalization
map to homogeneous affine localization, its exact kernel (A−1), the
resulting quotient equivalence, and its homogeneous fraction formula.
Under the existing natural comparison, the degree-one point maps to the
inverse of the dimension-free affine class, as required in Remark 4.16.
`RVAffineTensorEvaluation.lean` now constructs the geometric tensor map
into that homogeneous localization and its natural dimension-free target.
It and the bounded tensor map factor through the actual P−1 source
relation. The RES fraction formula and the geometric inverse-affine versus
bounded unit values on the degree-one point are proved. These remain
tensor constructions; neither global RV descent nor affine-localized
injectivity is assumed.

`RESAffineSpecialization.lean` constructs specialization A=1 on the
localized dimension-free target and proves that affine normalization
followed by this specialization equals the earlier ordinary specialization
on the entire RES ring and balanced tensor, including mixed-degree inputs.
It also proves the same formula through the actual tensor P−1 quotient.

`RVChartDisjointUnion.lean` constructs actual same-arity disjoint unions,
with original-base coordinate and partial-volume graphs, proper finite-
fibre coordinate maps, the exact weighted scissor square and additive
class formula. `RVChartUnionProperties.lean` proves preservation of finite
RES patterns and bounded domains, and the class formula in each measured,
ordinary, RES and bounded chart ring. `RVNamedTuples.lean` constructs named
raw RV tuple points in degree zero, including RV zero, and proves that
their measured RV and RES classes are the ring unit. These preparations
are for finite tagged coproducts; category identification remains open.

`RVTaggedCoproduct.lean` constructs actual tagged/padded coproducts for
any two same-degree charts of arbitrary tuple arities, using the named
RV constants zero and one. Their tag domains are proved disjoint, and
their measured RV class is the sum of the original classes. The tags and
padding have degree zero, so the intended object degree is retained.

`RVTaggedCoproductProperties.lean` proves that these tagged coproducts
preserve finite RES value patterns and bounded RV domains and gives the
ordinary RV class formula. This supplies actual RES and bounded objects
for arbitrary input tuple arities. Their category comparison is separate.

`RVTaggedCoproductClasses.lean` proves the class formula for tagged
coproducts in measured RES, ordinary RES and bounded measured RV rings,
retaining the original object degree and allowing arbitrary tuple arities.
This completes the concrete object and class calculations for these
finite coproducts; the equivalence with manuscript category presentations
and the global RV kernel/descent are still open.

`RVGraphComposition.lean` proves composition of actual original-base
partial RV graphs. The construction uses only real-coordinate pullbacks
and images while retaining the original Gamma parameters, with explicit
sort guards. `RVMeasuredIsomorphisms.lean` now proves actual inverse, composition and
product operations on measured isomorphisms, preserving the corrected-
weight equation. It also constructs arbitrary-degree underlying graph
composition and proves its actual tuple-map formula.

`RVPointProductIsomorphisms.lean` and `RVTaggedComponentIsomorphisms.lean`
construct actual measured isomorphisms removing each named tag/padding
component. `RVDisjointUnionIsomorphisms.lean` glues measured isomorphisms
on disjoint definable pieces. `RVChartRestrictions.lean` restricts actual
objects, preserves RES patterns and boundedness, and constructs the
measured isomorphism from the union of a partition to the original object.
The disjoint-union versus scissor presentation comparison is in progress.

`RVScissorComponents.lean` extracts actual domain partitions and matching
corrected weights from a weighted scissor square and builds the measured
isomorphisms between its matching pieces.
`RVTaggedPartitionIsomorphisms.lean` identifies tagged disjoint unions
with common-arity unions and identifies a tagged partition with the
original object. `RVDisjointInvariants.lean` proves that any additive
invariant respecting actual measured isomorphisms and tagged disjoint
unions respects every weighted scissor relation, including arbitrary
input tuple arities. The induced presentation equivalence is in progress.

`RVDisjointPresentation.lean` constructs the actual measured RV ring using
measured isomorphisms, products, empty objects and tagged disjoint-union
relations, proves its universal property and gives mutually inverse ring
maps to the weighted scissor presentation. The equivalence preserves
every object class. Thus the finite-disjoint-union versus weighted-scissor
presentation comparison is proved for full measured RV. The corresponding
remaining presentations and global RV tensor descent are separate.

`RVDisjointGrading.lean` proves full gradings on the two full measured RV
presentations and proves that their equivalence preserves every degree
in both directions. `RVAdmissibleFamilies.lean` proves that the actual
RES and bounded families are closed under products, definable restriction
and tagged disjoint unions, without assuming invariance of the family
predicate under arbitrary isomorphisms. The restricted invariant argument
is being extended using these verified closures.

`RVAdmissibleDisjointInvariants.lean` proves the disjoint-union-to-scissor
argument inside the verified RES and bounded families.
`RVFamilyDisjointPresentation.lean` constructs their intrinsic family
rings and universal property, with actual family objects as generators
and all weighted scissor relations proved. The maps to the separate
existing RES and bounded scissor rings are being checked.

`RESDisjointPresentation.lean` and `RVBoundedDisjointPresentation.lean`
now give actual objectwise ring equivalences from the separate intrinsic
measured RES and bounded RV disjoint-union rings to their existing
scissor rings. Their two ring maps are proved mutually inverse. The
remaining ordinary/Gamma presentation comparisons and global tensor
kernel descent are separate; the restricted equivalences' grading
compatibility is being checked.

`RVFamilyDisjointGrading.lean`, `RESDisjointGrading.lean` and
`RVBoundedDisjointGrading.lean` prove full gradings on the intrinsic
family presentations and preservation of every degree by both directions
of the measured RES and bounded RV equivalences.

`RVOrdinaryScissorComponents.lean` and `RVOrdinaryDisjointInvariants.lean`
prove ordinary scissor additivity from actual domain partitions and
original-base underlying bijections, without an equation on volume
forms. `RVOrdinaryFamilyPresentation.lean` and
`RVOrdinaryFamilyGrading.lean` supply the intrinsic ordinary family ring
and its full grading. `RESOrdinaryDisjointPresentation.lean`,
`RVOrdinaryDisjointPresentation.lean` and their `DisjointGrading` modules
prove the separate ordinary RES/full RV disjoint-union versus scissor
ring equivalences, objectwise and in every degree.

`RVDisjointRadiusQuotient.lean` constructs the accepted radius generators
and homogeneous ideal in the intrinsic bounded measured presentation,
proves independence from the chosen definable RV lift and vanishing at
radius zero, and proves that its quotient is ring-equivalent to the
existing radius quotient, with a degree-preserving comparison.
No global tensor kernel or Euler descent is asserted by this transport.

`RVDisjointPQuotients.lean` constructs the actual P class and ideal in
both intrinsic full RV presentations and proves separate quotient ring
equivalences for measured P=0 and ordinary P=1. The measured ideal is
homogeneous; the ordinary normalization is not assigned a grading.
`RESDisjointReduction.lean` constructs the actual measured and ordinary
value-fibre generator ideals in their intrinsic presentations and proves
that their images are exactly the existing ideals. The measured reduction
also kills the homogeneous affine line; the ordinary reduction retains it.
Both resulting quotient ring equivalences preserve all actual object classes.

`GammaRVFinitePartitions.lean` proves finite disjoint partition additivity
in the actual RV-lifted Gamma ring, retaining partial volume forms.
`GammaRVFiniteFamilies.lean` proves the finite-family class, sum and
product formulas and invariance under matching actual lifted partitions.
`FiniteFamilyBijections.lean` proves the decomposition of actual tagged
bijections into component bijections and its compatibility with a
commuting contraction map. `GammaRVFamilyIsomorphisms.lean` applies this
to actual original-base Gamma bijections and their actual RV lifts;
finite-family isomorphisms preserve their ring classes without adding
Gamma coordinates. `GammaRVFamilySharp.lean` builds actual RV charts
for finite Gamma unions using degree-zero tags and proves their sharp
class formulas, full-degree membership and isomorphism invariance.

`GammaRVFiniteUnionPresentation.lean` constructs the ring on finite
formally tagged Gamma unions, including disjoint-union additivity,
single-chart scissor relations and all actual contracted family
isomorphisms. Its objectwise maps to and from the single-chart ring are
proved mutually inverse. `GammaRVFiniteUnionGrading.lean` proves the full
grading and degree preservation in both directions;
`GammaRVFiniteUnionOperations.lean` constructs empty families, formal
finite unions and Cartesian products with their class formulas. Bounded
and finite Gamma families are still being checked intrinsically. This
presentation comparison does not prove the global tensor kernel/descent
or degree-one point nonvanishing.

`GammaBoundedRVPartitions.lean` and `GammaFiniteRVPartitions.lean` prove
finite partition additivity intrinsically in the bounded and finite
Gamma rings. All restrictions retain a proved domain bound or finite
support. `GammaRestrictedRVFiniteFamilies.lean` proves that actual
RV-contracted family bijections preserve the separate intrinsic class
sums. Neither proof uses injectivity into the full Gamma presentation.

`GammaBoundedRVFiniteUnionPresentation.lean` and
`GammaFiniteRVFiniteUnionPresentation.lean` construct their respective
finite formally tagged union rings and prove objectwise ring equivalences
with the single-chart rings. The corresponding `FiniteUnionGrading`
modules prove full gradings and degree preservation in both directions;
the `FiniteUnionOperations` modules construct empty families, formal
unions and Cartesian products and prove their class formulas. Thus the
finite-family presentation comparisons now cover all three actual
RV-lift-restricted Gamma rings. Sharp-map and diagram compatibility is
being transported across the checked equivalences. Global tensor kernel
descent and degree-one point nonvanishing remain open.

`RingPresentationTransport.lean` proves transport of ring maps,
compositions, exact kernels and grading compatibility along proved
presentation equivalences. `IntrinsicPresentationMaps.lean` constructs
all three intrinsic Gamma sharp maps and the RES/bounded/full inclusion
maps, proves their single-object formulas and the complete sharp squares.
`IntrinsicPresentationGradings.lean` proves degree preservation for all
nine maps. `CoactionQuotientEquivalence.lean` proves that matching
homogeneous quotients preserve degrees in both directions and transports
ideal coefficient closure. `IntrinsicQuotientGradings.lean` applies this
to the intrinsic measured P quotient and both RES reductions, and proves
the two-sided grading comparison for the radius quotient. The ordinary
P=1 normalization is inhomogeneous and has no assigned grading here.

`IntrinsicFiniteGammaAlgebras.lean` constructs the finite-Gamma algebra
structures on the intrinsic presentations, their algebra equivalences
with the existing models, and compatibility with the actual finite-union
coefficient maps. `IntrinsicBalancedTensors.lean` constructs the full and
bounded balanced tensors on those intrinsic factors, proves algebra
equivalences with the existing balanced tensors, and constructs the
actual product comparisons with pure-tensor formulas and commuting
squares. `IntrinsicBalancedGradings.lean` constructs their full gradings,
proves homogeneous pure tensors have the sum degree, and proves degree
preservation by both directions of each tensor equivalence and by both
product comparisons. These are presentation equivalences of source
tensors, not tensor-to-RV isomorphisms; global RV kernel descent remains
open. The intrinsic Euler evaluations are being transported next.

`IntrinsicBalancedEvaluations.lean` constructs the measured and bounded
ordinary Euler evaluations on the intrinsic tensors, with the expected
pure-tensor formulas, full degree preservation, RES-factor restrictions
and bounded independence of Euler choice. The bounded construction has
no canonical-structure premise. `IntrinsicBalancedSpecialClasses.lean`
constructs actual P, h and accepted-radius preimages in those sources,
proves their degrees and comparison formulas, lift independence and the
zero-radius source equality, and proves P and all accepted radius
preimages evaluate to zero. The geometric h value is the actual reduced
degree-one point +[1], and its bounded value is zero; point nonvanishing
is not asserted.

`IntrinsicBalancedRadiusQuotient.lean` constructs the homogeneous source
radius ideal and its graded quotient, with a degree-preserving equivalence
to the existing source quotient in both directions. The actual product
comparison and canonical-free ordinary evaluation factor through it as
graded maps, with the RES restriction and bounded independence of Euler
choice proved. This is source-radius-ideal descent and does not establish
vanishing on the full RV comparison kernel.

`IntrinsicBalancedPQuotient.lean` constructs the homogeneous P ideal and
its actual graded quotient on the intrinsic full tensor. The product
comparison and both measured evaluations factor through it as graded
maps. The RES restriction proves that both evaluations from this source
quotient are surjective. The quotient and the intrinsic measured RES
target satisfy 0≠1, using the established zero-degree weighted count;
this does not prove nonvanishing of the degree-one point or identify the
source quotient with an RV quotient. Global RV kernel descent remains open.

`RVFiniteOrdinaryCounts.lean` proves finite integer cardinality invariant
under actual underlying RV bijections and ordinary scissors, and proves
multiplicativity. `RVOrdinaryZeroCount.lean` extends this to actual ordinary
RV/RES rings by zero on positive degree and factors it through the ordinary
RES fibre ideal, proving 0≠1 in that target. `RESOrdinarySurjectivity.lean`
proves the actual measured-to-ordinary forgetful map is surjective and
therefore proves surjectivity of both intrinsic bounded evaluations,
before and after the source radius quotient. No canonical-structure
premise is used. `IntrinsicBoundedNontriviality.lean` proves ordinary target,
bounded tensor, source-radius quotient and RV-radius quotient nontriviality
from degree-zero counts. The measured source P quotient's 0≠1 proof is
also strengthened to remove all Euler-linearity and saturation premises.
These counts vanish on the degree-one point; its nonvanishing is still open.

The measured Gamma finite-union comparisons are complete for full,
bounded and finite supports. An ordinary Gamma presentation with no
volume-preservation condition remains a separate §4.1 construction; the
existing ordinary evaluations on measured Gamma sources forget volume
forms, but that does not identify those source categories.

`GammaOrdinaryCharts.lean` constructs actual Gamma charts without volume
forms and original-base RV-contracted bijections without a volume
equation. `GammaOrdinaryRing.lean` constructs their ordinary scissor ring
and proves the measured-to-ordinary Gamma forgetful map surjective.
`GammaOrdinaryGrading.lean` proves the full grading and degree preservation
of forgetting. `GammaOrdinaryEulerEvaluation.lean` constructs both actual
numerical Euler evaluations, proves the χ(I)T^n formula, and proves whole-
ring compatibility with the earlier evaluation on measured Gamma sources.
Ordinary isomorphism invariance uses the independently proved numerical
Gamma definable-bijection invariance, not a volume-preservation condition.

`GammaOrdinarySharpObjects.lean`, `GammaOrdinarySharpScissors.lean` and
`GammaOrdinarySharpRingMap.lean` prove the actual ordinary sharp unit,
product, empty and scissor formulas, the set-level scissor functoriality,
and the graded sharp ring map to ordinary RV. Its measured-forget square
commutes on the whole source. `GammaOrdinaryFiniteCharts.lean` constructs
actual finite ordinary Gamma objects and their full RES fibres, with unit
and product class formulas. Their coefficient ring, ordinary tensor and
finite-family presentation comparisons are still being constructed.

`GammaOrdinaryFiniteRing.lean` constructs the ordinary finite-Gamma
coefficient ring and proves the measured finite-Gamma forgetful map
surjective. Its full grading and the actual maps into ordinary Gamma/RES
are proved in `GammaOrdinaryFiniteGrading.lean`,
`GammaOrdinaryFiniteMaps.lean` and `GammaOrdinaryFiniteMapGradings.lean`.
Both measured-forget squares and the ordinary sharp square commute.
`GammaOrdinaryRESEvaluation.lean` constructs graded Euler maps into the
ordinary RES fibre quotient and proves full balancing on the entire
ordinary finite coefficient ring by descent along the proved surjection.

`GammaOrdinaryAlgebras.lean` constructs the ordinary coefficient algebra
structures. `RVOrdinaryBalancedTensor.lean` now constructs the actual
ordinary RES/Gamma tensor over that ordinary finite-Gamma ring, its actual
ordinary RV product comparison, and both Euler maps with the manuscript
χ(I)[G_m]^n formula and RES restriction. `RVOrdinaryBalancedGradings.lean`
proves the full grading and degree preservation of comparison and both
Euler evaluations. `RVOrdinaryIntegerTensor.lean` constructs the component
maps first over the integers, proves that the map to the finite-Gamma-
balanced tensor is surjective, and proves whole-ring comparison and Euler
compatibility. This is balancing-source descent, not the unresolved global
ordinary RV kernel descent. Ordinary Gamma finite-family presentation
comparisons also remain separate.


Ordinary Gamma finite disjoint unions now have separate presentation
equivalences for the full ring and the finite coefficient ring, preserving
all degrees. Actual sharp family objects are constructed. The ordinary
annulus vanishes by an actual RV-lifted ray isomorphism. Forgetting volume
on balanced tensors is surjective and graded, and commutes with RV
comparison and both Euler maps. The bounded source-radius quotient maps
to that ordinary tensor because its radius preimages already vanish.
Point/affine normalization is also constructed on its P−1 source quotient.
These are supporting constructions; global RV kernel descent remains.


Concrete unary coefficient-coordinate translations now give actual measured
RV product isomorphisms, so their homogeneous ideals lie in the full and
bounded RV comparison kernels. A retained coefficient coordinate supplies
the multiplier; no original-base RV representative is selected. The full
measured Euler maps and the direct bounded ordinary Euler maps kill the
respective ideals. Ordinary Gamma translations of every finite arity also
have proved numerical Euler invariance and a homogeneous ordinary-tensor
evaluation ideal. These are kernel inclusions and annihilation statements;
the full reverse inclusion and global descent are still open.


The actual ordinary tensor comparison is now a ring equivalence on its
whole degree-zero subrings (`RVOrdinaryBalancedZeroDegree.lean`). Its kernel
is homogeneous and every kernel element decomposes into positive-degree
homogeneous kernel elements. The finite Gamma coefficient inverse is
constructed directly without volume forms. This reduction does not supply
the missing positive-degree reverse kernel inclusion.


The finite cylindrical decomposition construction is now complete for the
project's graph/band/ray/line cell constructors. Every original-base
definable Gamma set has such a finite disjoint decomposition; each piece is
nonempty, its recursive dimension is at most the ambient arity, and the
constructed geometric Euler integral is the alternating dimension sum,
independent of the chosen decomposition. These constructors do not impose
continuous endpoints; no independent topological-dimension identification
is claimed. The ordinary coefficient-translation ideal is also proved to
be the image of the measured coefficient ideal and to lie in the actual
ordinary comparison kernel and both Euler kernels.

The T001 approval dependency is cleared. The remaining dependency is the
concrete transport of its positive presentation to these local chart rings
at the manuscript's parameter scope, as recorded above. Degree-one point
nonvanishing is also separate; the measured maps' stated values alone do
not prove that they are distinct.

The ordinary RV range statements are also proved relative to the same
transported T001 input (`RVT001OrdinaryRanges.lean`). Both graded Euler maps
are onto the actual reduced RES ring, and the bounded restriction and
radius quotient maps are onto it. Point and homogeneous affine
normalizations are onto their intended targets. The subsequent geometric
map has exactly the range of the natural affine-localization comparison;
no surjectivity or injectivity of that comparison is inferred.


The author approved the Section 4 T001 follow-through and instructed completion
of the section. Independent point-nonvanishing work now uses the checked
companion residue-purity theorem, Mathlib's Lefschetz specialization and
finite-field rational-point counts. Definable maps over a Galois base preserve
rational points; finite formulas and their parameters specialize together.
These supporting lemmas do not yet establish nonvanishing of the RES point.
Section 3 is concurrently checking the Gamma-to-RV map and its monomorphism
claim. The local sharp maps retain actual RV lifts, and matching the final
upstream category presentation remains explicit.


The pure-field nonvanishing milestone is now proved without an added theorem
input. `FiniteFieldPointDiagram` specializes every finite diagram of actual
pure-field definable bijections, with common parameters, to arbitrarily large
finite Galois point sets. `FieldAffineNontrivial` proves that the unit survives
after killing the affine-line class. `FieldFiniteCharacters` and
`FieldAffineTranscendence` prove that the affine-line class is transcendental
over the integers in this pure-field presentation.

The checked residue-purity theorem now gives actual pure-field codes for
every original-base RES chart domain (`RVResiduePullback`,
`RVResidueScaledCovers`, `RVResidueFullFibres`,
`RVResidueFiniteNormalization`, `FieldTaggedFamilies`, `RVResidueCodes`,
`RVResidueChartCodes`, `RVResidueJoinedCovers`). The decoders are actual
bijections, their finite pieces are scaled coordinate maps, and zero RV
coordinates are retained. Auxiliary representatives in this geometric proof
are not claimed definable over the original base. Compatibility with all
RES ring/reduction relations and nonvanishing of the actual degree-one
RES point remain separate. No numbered retraction is marked complete.

The latest Section 3 discussion fixes the intended full-preimage Gamma
morphism convention and confirms that horizontal coefficient monicity is
not needed for the later tensor/evaluation descents. Its proposed
Reichstein--Youssin proof is not imported as a new input here. The local
original-base presentation adapter remains to be instantiated.


## Actual point nonvanishing and assembled statements — November 12

`RESPointNonvanishing.point_ne_zero_acvf00` proves that the actual measured
degree-one point survives the fibre/affine reduction. Its hypotheses are
canonical totalization and ACVF(0,0), with the original real/Gamma base
unrestricted; no RV representative is asserted definable there. The proof
constructs pure-field codes, checks their isomorphism, empty, unit, product
and scissor relations, then kills the actual fibre and affine relations.
Finite-field specialization proves the target quotient nonzero. There is
no HK nonvanishing theorem or new external theorem input.

`RVT001RetractionStatements.proposition_4_7` and `.proposition_4_15` assemble
all clauses of the two main graded retractions relative to the precise
transported T001 interfaces. Proposition 4.7 includes distinctness with
proved point nonvanishing, rather than an extra nonvanishing premise.
Proposition 4.15 uses the full ordinary presentation and needs no bounded
tensor injectivity or bounded tensor kernel theorem. These remain relative
to uninstantiated upstream presentation hypotheses; they are not reported
as unconditional completed numbered formalizations.

The independently verified nonvanishing justification is now in the main
proof of Proposition 4.7, under the author's standing authorization for
established corrections and proof completions. It changes no statement.
Three TeX passes and the resolved nine-page extract (printed pp. 39–47)
check; the full manuscript remains 93 pages. The accepted colored review
copy is preserved.


The ordinary residue trace and affine separation now check as well.
`RESOrdinaryResidueTrace` retains the affine line while descending through
ordinary fibre relations and forgetting degree. `RESAffineSeparation`
proves that the actual dimension-free affine class and its inverse are
different from one after localization. `RVT001NormalizedDistinct` applies
this to the two normalized ordinary RV maps, relative to the same explicit
T001 input. No injectivity of the natural localization comparison is used.

The remaining critical dependency for unconditional main retractions is
the original-base T001 adapter. The upstream project currently reports its
positive presentation at canonical, saturated, small VF/Gamma-generated
Gamma-ground scope, while these local rings allow arbitrary original
real/Gamma bases. A scope change or a claim that all Gamma names admit
definable RV lifts is not inferred. Classical continuous-cell/topological-
dimension identification and the geometric noninjectivity/nonsurjectivity
claims of Remark 4.4 are also not certified by the supporting constructions.
