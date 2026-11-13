# Section 4 cited inputs

The author accepts bibliography items 18–22 as explicit, replaceable inputs.
HK Euler characteristics, invariance and Fubini theorems are not inputs.
The governing policy is the repository's `ACCEPTED-CITED-RESULTS.md`.

## Unary value-group linearity

- Existing input: `DiamondIntegral.Section2.GammaPiecewiseRationalAffineInput`
  in `section 2/CitedGammaLinearity.lean`.
- Source: [18], Yimu Yin, *Integration in algebraically closed valued
  fields*, proof of Lemma 3.18; arXiv:0809.0473v2. The cited context uses
  quantifier elimination and piecewise rational-affine Gamma functions.
- Exact content: in ACVF(0,0), with a nontrivial definable ground value
  group, a unary definable graph on D has a finite cover by equations
  T(x)^qᵢ = cᵢ x^pᵢ, where qᵢ ≠ 0, pᵢ is integral and cᵢ is an actual
  Gamma value. No definable RV representatives of the coefficients are
  asserted.
- Use: `GammaUnaryBijections.unary_bijection_invariance` takes that input
  as the explicit argument `linear`, together with the characteristic and
  original-base nontriviality hypotheses. It uses the input only to obtain
  a finite power-law cover. `GammaUnaryDescent` and
  `GammaWeightedPushforward` use the same input to construct original-base
  unary image functions. The exceptional-value bound, Gamma counting,
  descent and finite level-set decomposition are proved here.

`nontrivial_commonBase` preserves nontriviality while the graph is
temporarily represented over `commonRealNames B`. Those RV representatives
are auxiliary proof parameters, not claimed definable over B. The conclusion
compares the canonical Euler values over the original B. Independence of
the representation and auxiliary base is proved in `GammaEulerSets.lean`.

The following parts are proved here without this linearity input: full
power-law cell definability, disjoint refinement, order transport, the
actual unary fibre integration identity and preservation of total Euler
integrals for finite power-law pieces. The bijection argument then computes
every actual fibre as a singleton or empty. No Euler-invariance conclusion
is supplied as an assumption.

The verifier prints the complete input definitions alongside every Section
4 declaration and audits their logical axioms. This is a proof relative to
the authorized background, not a claim that its source paper has been
formalized here. Identification with cell-dimension Euler values and the
actual graded retraction maps remain separate obligations.

## Uniform Gamma families

The uniform-cut, unary-coordinate family integration and canonical-boundary
proofs do not use the Gamma-linearity input. They derive finite thresholds
from the checked companion C-minimality proof, and derive uniformity from
genuine model-theoretic saturation. Both real and Gamma base smallness,
ACVF(0,0), and the saturation cardinal are explicit in the relevant theorem
types. The finite-cover argument temporarily uses common real codes;
Gamma quantification proves the output level sets and sorted-point graphs
over the original base. These are not assumed Euler or Fubini results.

## Two-coordinate Fubini

`GammaUnaryProjection` uses the same explicit Gamma-linearity input to
produce finite power-law pieces for each actual unary boundary map. Its
source and target weights are actual finite-jump functions and may have
extra endpoints. The weighted projection identity is proved from those
pieces. `GammaKernelDecomposition` constructs the full point-and-ray
expansion and all unary projection witnesses. `GammaFubiniTwo.fubini_two`
then proves equality of the two actual iterated integrals in dimension two.
No decomposition, Euler/Fubini identity or HK theorem is assumed as an input.

## Finite-dimensional integration

`GammaParametricFubini` applies the proved two-coordinate result over the
original base extended by the actual finite Gamma parameter tuple. Smallness
and nontriviality are proved to persist. `GammaFubiniPermutation` combines
this with a finite-permutation generation proof, so every coordinate order
gives the same actual iterated integral. `GammaPrefixIntegration` identifies
the iterated result with actual fibres. `GammaHigherPushforward` uses the
actual graph and singleton-output computation to prove total-integral
preservation from Gamma^n to Gamma. These results retain the explicit
linearity, characteristic, saturation, base-smallness and nontriviality
hypotheses; no higher-dimensional Euler theorem or HK input is added.

`GammaBlockFubini` proves the corresponding identity for arbitrary finite
coordinate blocks. `GammaPointFamilies` and `GammaBijectiveRelations` then
compute the actual graph fibres and derive general definable-bijection
invariance in arbitrary finite arities. `GammaIntegralCongruence` and
`GammaProductFamilies` prove base-presentation independence and the product
formula from actual fibre evaluation and additivity; these two modules do
not need the Gamma-linearity input.

The finite-dimensional bounded comparison uses no Gamma-linearity input.
`GammaRadius` constructs a definable proper radius with exactly the
symmetric-box sublevel sets. `GammaRadiusProfiles` compares the two actual
profiles on its bounded fibres. `GammaHigherProjection` and
`GammaSymmetricTruncation` identify actual source restrictions with unary
profile truncations. `GammaBoxStabilization` then proves stabilization in
every finite dimension, using the explicit authorized linearity input only
through the proved Fubini/pushforward identities. The radius need not be
definable over the original base: it is named in a finite Gamma extension,
with proved smallness and base-presentation independence. No Archimedean
assumption is introduced.

`GammaProfileBijections` applies proved finite-dimensional Euler invariance
to the actual level-one fibre sets. `GammaMeasuredProfileInvariance` checks
the corrected-weight equation from the manuscript Gamma-Jacobian formula.
The constant-pushforward and counterweighted-ray computations do not need
the Gamma-linearity input: they use only actual fibres and the constructed
coordinate integrals. The actual RES target assignments and graded category
presentation are not supplied as theorem inputs or declared complete.

`GammaBoundedMapImage` reuses the proved Section 2 theorem
`lemma_2_41_gamma_raw`, not a new bounded-image input. It builds the full
raw-code domain and graph over common real names and proves smallness and
nontriviality there. The reused theorem's canonical-structure hypothesis
is explicit. `GammaBoundedProfileRange` obtains the volume bound from that
result and constructs the actual bounded-ring-valued profile; its Euler
value is proved equal to the source integral.

`GammaSumFibres` computes actual weighted sum-map sections by the proved
prefix-fibre theorem. `GammaPushforwardConvolution` combines that identity
with the proved projection formula over an explicit finite Gamma extension,
then uses base-presentation independence to identify the result with the
previously constructed unary convolution. `GammaProfileProducts` applies
it to actual product sets and corrected volume forms. No convolution,
product-profile or Fubini theorem is supplied as an additional input.

`GammaCellSections` and `GammaCellUnboundedSections` compute actual graph,
band, ray and line sections from the existing finite-jump functions.
`GammaCylindricalCells` and `GammaCellFormula` prove (-1)^dimension and its
sum for supplied finite cylindrical decompositions. These calculations do
not use Gamma-linearity, cell-decomposition existence or an Euler theorem
as inputs. They do not assert existence of classical o-minimal decompositions
or identify a separately defined topological dimension.

`GammaChartPresentation` defines its generators as actual weighted Gamma
charts with partial definable volume graphs. Its relations are explicit
products, unit, empty domains, scissors and actual volume-preserving
definable bijections. Each relation is proved to vanish before quotient
lifting. This is an auxiliary presentation with all such bijections, not
an assumed copy of the manuscript Grothendieck category; identification
with the additional RV-lift restriction remains open.


The bounded chart map uses the proved 2.41 bridge to enter the actual bounded
polynomial source; no bounded profile or ring map is assumed as an input.
Its independence of the Euler choice is proved on generators and extended
to the entire generated subring. The unbounded specialization is constructed
from the actual endpoint projection and the explicit target weight
character. Its comparison with the bounded specialization for the trivial
character is a proved equality of maps, not an additional input.
The generic target ring and character do not implement the manuscript RES
target or a tensor-descent theorem.

`GammaRVLifts` uses the checked RV carrier, its group operations and
first-order definable-closure laws in the companion library. The liftable
value subgroup is the actual image of original-base definable RV units.
A value of a definable RV point is proved Gamma-definable by the checked
named-code theorem over the closure base and parameter elimination. No
claim that every definable Gamma value lifts is supplied or inferred.

`GammaRadiusAnnulus` identifies the actual annulus indicator with the
difference of two actual rays, so its Euler value and bounded chart
specialization are proved zero, including zero radius. It is only the
Gamma factor calculation, not an assumed vanishing theorem for P_gamma.
`GammaRVChartPresentation` defines the restricted chart isomorphisms by
actual original-base definable RV graphs, bijections between full proper
preimages and the contraction equation. Its profile maps are obtained by
a proved inclusion of relation ideals, not by a tensor-isomorphism input.
Finite tagged unions and the graded category identification remain open.


`RVMeasuredCharts` uses actual original-base real/Gamma definability of
domains, finite-fibre coordinate graphs and partial volume graphs. RES
means finite full value patterns, including the infinity class. Its
isomorphism condition is the proved equivalent corrected-weight form of
the manuscript volume equation. Degree-zero finiteness follows from the
actual finite coordinate fibre, without a splitting or definable-point
assumption for finite RV sets. `RVPointChoices` builds actual definable
singleton graphs and the volume-preserving isomorphism for two original-base
definable lifts of the same value. No RV Grothendieck ring or tensor theorem
is assumed by these object calculations.


`RVSharpCharts` constructs the actual full proper RV preimage of a
weighted Gamma chart, with identity finite-fibre coordinate map and its
original-base partial volume graph. Its isomorphism map uses the actual
RV-lift bijection and contraction equation, then proves the measured
corrected-weight equation. No existence of arbitrary RV lifts or tensor
comparison is supplied as an input.


`GammaTupleMaps` derives tuple-map graphs, images, preimages and scalar
compositions from actual coordinate graphs over the original base.
`GammaTranslation` proves invariance of both actual finite-dimensional
Euler integrals under Gamma-definable translations. It constructs the
compensated target volume, proves its original-base definability and volume
equation, and obtains equality of actual profiles from the proved bijection
invariance. RV liftability is not needed for these Gamma identities.
The geometric tensor kernel-generation theorem and full RES/RV descent
remain separate; no §3 paper-level kernel argument is imported as an axiom.


`RVMeasuredGroup` is the explicit additive scissors quotient on actual
measured RV chart objects, with actual isomorphisms and weighted scissors
relations. Its additive universal property and uniqueness are proved.
`RVRadiusGenerators` constructs P_gamma in that additive presentation,
proves independence of the original-base definable lift and proves the
zero-radius class is zero. `RVMeasuredBounds` obtains actual domain bounds
for all RES charts from finite full value patterns and finite ordered-group
bounds; no Archimedean assumption or definable point selection is used.
The graded RV product ring, bounded category identification, P_Gamma ideal,
forgetful images and global retraction are not supplied by these modules.

`RVRadiusBounds` proves boundedness of the actual annulus and singleton
charts and places P_gamma in the additive span of bounded chart classes
in the ambient scissors group. No injectivity of the bounded-category map
or identification of this span with a separate bounded presentation is
assumed or asserted.


`FiniteTupleGraphProduct` supplies the explicit finite-coordinate shuffle.
`RVRealProducts` uses the actual raw-coordinate images of product graphs
to prove original-base definability. `RVVolumeMaps` multiplies partial
Gamma volumes by representing the two auxiliary values by full RV-code
fibres and projecting them out. It also proves coordinate restriction.
`RVMeasuredProduct` constructs the actual product domain, finite-fibre
coordinate map and partial volume graph. `RVMeasuredProductProperties`
proves multiplication of corrected weights and preservation of finite RES
patterns and doubly bounded domains. No product, representative-selection,
RES ring or tensor theorem is assumed by these constructions.


`RESChartRing` constructs its ring from actual RES objects and their
actual isomorphism/scissors/product/unit relations. Its generic invariant
is a universal-property argument, not an assumed RES interpretation.
`RESWeightCharacter` realizes the character by actual zero-degree weighted
units and proves multiplication by an actual RV isomorphism.
`RVCoordinateMaps` and `RVWeightScaling` construct actual original-base
graphs and prove the volume-scaling product isomorphism on every object.
`RESFibreObjects` obtains actual value-fibre RES objects from finite Gamma
support. Neither a definable RV lift of every Gamma value, a splitting of
finite RV sets, a graded category identification nor an HK tensor theorem
is assumed.


`RESMeasuredReduction` imposes the actual measured value-fibre relations
and the degree-one affine-line class in the concrete RES chart ring.
`RESUnboundedPsi` composes the proved source specialization with the
constructed original-base weight character and actual torus class. Its
assignments and counterweighted-ray values use actual weighted RES objects.
`GammaSingletonProfiles` computes the actual singleton profile and its
homogeneous polynomial by proved support congruence, constant pushforward
and singleton integration. It adds no RV-lift, linearity, tensor or HK
input. Grading/category identification, nonzero point class and global RV
descent are still separate obligations.

`RESFiniteBalancing` identifies the proved singleton polynomial, after ψ,
with the actual measured RES fibre object by the constructed value-fibre
ideal. This degree-one balancing statement does not assume RV lifts of
Gamma constants, tensor injectivity, kernel generation or global descent.


`RVForgetScissors` proves the projection from weighted packed graphs to
underlying domains preserves a scissor square, using injectivity on the
union graph. `RESOrdinaryRing` constructs the ordinary chart ring and the
measured forgetful map from this proved compatibility. Its redundant
volume labels do not split finite RV coefficients. `RESOrdinaryReduction`
proves the measured fibre ideal maps to zero in the ordinary value-fibre
quotient. It retains the affine-line class for the bounded target.
`RESBoundedPsi` specializes the actual bounded polynomial source at its
actual torus class and proves the object formula and Euler-choice
independence on the full bounded chart subring. The actual bounded
singleton polynomial is identified through the injective bounded inclusion;
`RESBoundedFiniteBalancing` compares its image with the actual measured
RES fibre under the constructed forgetful map. Global tensor descent,
grading and category identification remain separate obligations.


`GammaCylindricalDecompositionExistence` now constructs finite original-base
cylindrical decompositions by induction using the checked finite boundary
graph partition, actual stack coverage/disjointness and base refinement.
`GammaCylindricalCellGeometry` proves nonemptiness and ambient dimension
bounds. `GammaConstructedCellEuler` applies the proved cell value formula
to this constructed decomposition and proves independence of the dimension
sum. This uses ACVF(0,0), saturation and explicit base smallness, with no
Gamma-linearity or cell-decomposition theorem supplied as an input. Endpoint
continuity and topological-dimension identification are not claimed.


## Author-approved project result T001

The author explicitly approved Section 3's corrected Proposition 3.18
(T001) on November 12. This is an upstream result of the current project,
not an accepted HK theorem or a new external citation. The positive
surjections and coefficient-translation kernel congruences are primary;
the groupified kernel ideals are their consequences.

`ApprovedT001Presentation.Ordinary` and `.Measured` state the exact local
transport interfaces: the actual balanced comparison is surjective, and
its kernel is contained in the proved actual coefficient-translation
ideal. The opposite inclusion was independently proved in Section 4, so
the interface gives equality. Scalar constant-value definable functions
are covered by graph adjunction, without choosing a definable point of
the coefficient object. Every new RV descent takes its interface value
explicitly. Both values are now proved by `Section3T001Integration`; the
linked retraction statements require neither value as an input.

The finalized actual tensor kernels retain arbitrary original real/Gamma
bases, canonical ACVF00, saturation, both base smallness conditions and
nontrivial definable Gamma. VF generation is an extra context condition for
VF lift applications. The categorical-to-chart presentation transport is
constructed without introducing that extra condition.

The Section 4 work after this approval proves graded descent, actual RV
Euler maps with explicit RES and P/h formulas, point/affine normalization,
the alternative Remark 4.8 descent, and the bounded measured restriction
and radius commuting square relative to that precise upstream interface.
In particular the bounded construction uses only the full ordinary
presentation, not a separately assumed bounded tensor presentation. The
new structures and all theorem types are printed by the ordinary complete
Section 4 declaration audit.

The approved T001 manuscript statement and both positive proofs have now
been synchronized verbatim from the upstream adoption record, independently
of the remaining Lean presentation transport. Its exact source block and
provenance are retained in `reference/T001-approved-upstream.tex` and
`verification/t001-upstream-review.json`. The ordinary range theorems also
retain this explicit transport input; they make no injectivity or
surjectivity assertion about the natural affine-localization comparison.


## Current-project Section 3 results accepted as given — November 12

The author explicitly instructs: “take unformalized results in sectrion3
as given for now.” `ApprovedT001Presentation.Ordinary` and `.Measured`
are therefore accepted replaceable background inputs at their exact local
original-base formulations, rather than blockers awaiting compiled adapters.
No tensor injectivity or RV lift for an arbitrary definable Gamma value
is introduced. Propositions 4.7 and 4.15 have all clauses proved relative
to this authorized Section 3 background.

`Section3GammaAffineInput.Input B` states the rational-affine Gamma normal
form used in the Section 3 analysis (pure divisible ordered-group/QE
background). For an original-base definable map T:Gamma^n -> Gamma, it
supplies finitely many global branches a_i with
T(x)^q_i = c_i * product_j x_j^(p_ij), q_i != 0, integer p_ij, and
original-base Gamma-definable c_i. There is no definable-RV-lift claim.
This structural normal form is a replaceable Section 3 input under the
new instruction. It contains no continuity, cell decomposition, dimension
sum or Euler conclusion.

`GammaRationalAffineContinuity` proves continuity and original-base
definability of those explicit branches. `GammaContinuousPartitions`
constructs disjoint simultaneous continuity regions. Boundary-stack
refinement and induction then prove continuous cell decomposition in
`GammaContinuousDecomposition`; its Euler formula follows from the
previously proved actual fibre calculations. No HK cell or Euler theorem
is used. The cell dimension is the usual recursive graph/interval
dimension; an additional covering-dimension theory is outside the
main-text claim.


## Completed local boundary — November 12

The earlier remaining-work notes in this file are historical. Relative to
the author-accepted Section 3 inputs, all Section 4 main-text obligations
are now proved. In particular:

- `GammaContinuousDecomposition` proves continuous cells and their Euler sum.
- `RESAffineNonsurjective.remark_4_4` proves nonsurjectivity on the actual
  original-base RES presentations. Its coordinate-cover and uniform-fibre
  bounds reuse checked dimension/rank, exchange and saturation results.
  Their finite-field growth estimates, finite-diagram specialization,
  homogeneous-component transport and localization obstruction are proved
  locally. No new cited theorem, dimension-growth conclusion or
  nonsurjectivity assertion is assumed.
- Both complete retraction propositions and the bounded commuting diagram
  are proved relative to the exact ordinary/measured T001 interfaces.

That temporary acceptance policy permitted completion before the upstream
proofs were available. The finalized adapters are now compiled as recorded
below.
The removed injectivity claim's referee counterexample is review commentary;
formalizing its particular varieties is outside the corrected main text.


## Audit against finalized Section 3, commit 37c8361

The finalized Section 3 sources and their source-matched verification
receipt were inspected after the author reported completion. Both actual
ring tensor kernels are now exported, with exact coefficient-translation
ideals and evaluation descent. Their characteristic, canonical structure,
saturation, base smallness and nontrivial-Gamma hypotheses match the
Section 4 uses. No corrected Section 4 statement changes. The approved
T001 statement and both proofs remain verbatim after synchronizing the
other approved Section 3 manuscript edits.

The finalized source uses categorical positive Grothendieck semirings and
ring completions. Section 4 uses actual chart/scissor presentations.
`Section3T001Integration` now constructs the complete conversion: actual
ordinary/measured RES, Gamma, finite-Gamma and RV ring equivalences; scalar
squares; source tensor equivalences; comparison squares; and transport of
every elementary native coefficient pair into the chart coefficient ideal.
Availability is transported by an actual definable function on the RES
coefficient and graph adjunction. No original-base point is chosen.

`Section3PresentationAudit` applies the finalized kernel and surjectivity
proofs to those instantiated records, yielding both local T001 interfaces.
`Section3LinkedRetractionStatements.proposition_4_7` and `.proposition_4_15`
therefore require no T001 input. All original-base, saturation, characteristic,
smallness and nontrivial-Gamma hypotheses remain visible in their types.
No mathematical departure or new manuscript edit was needed.

General rational-affine Gamma normal form remains explicit accepted QE
background. Section 3's integral-affine contraction classification is not
a proof of that different statement. Later external [18] lift/integral
inputs, including unfinished measured Section 7, retain their already
authorized scope. No HK input is introduced.
