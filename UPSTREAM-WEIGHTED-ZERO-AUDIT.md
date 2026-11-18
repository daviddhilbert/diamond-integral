# Weighted degree zero: upstream correction and this consumer

**November 16 update:** both corrected upstream releases are published and the
consumer pin migration is recorded in
[the compatibility audit](verification/upstream-weighted-zero-upgrade/README.md).
Its current receipt and the refreshed section receipts supersede the old-pin
compatibility boundary below. The corrected Integration HK kernel has
RV-valued densities. The subsequent local Gamma-valued proof now constructs
all four measured records; see [the completion note](<section 3/verification/GAMMA-KERNEL-COMPLETION.md>).
The historical conditional boundary below is superseded by those producers,
not by identifying the RV-valued and Gamma-valued density categories.

Historical source review, November 15, 2026. Read this with [HANDOFF.md](HANDOFF.md)
before continuing Section 7 or changing dependency revisions.

The author approved a migration in Integration in ACVF and Special
transformations to measured degree-zero objects retaining their weights,
including definable families of weights. The upstream review identified a
degree-one factorization that loses its density when the proposed factor
has degree zero and that category is treated as ordinary, unweighted RV[0].
The author instructed those projects to begin their corrections. This note
does not certify that their migration has been implemented or published.

## The mathematical issue

For a positive-degree weighted object, an elementary relation is often
factored through an object of one lower degree. At source degree one that
factor has degree zero. Its modified volume form cannot be discarded.
Excluding degree-zero source objects does not solve this degree-one case.

In a Gamma-valued convention, let Z_gamma be a degree-zero singleton with
weight gamma, and let P_gamma and C_gamma denote the corresponding
constant-density twists of the degree-one point and cone. When the weighted
zero coefficient is genuinely present and mixed multiplication retains it,

~~~text
P_gamma = Z_gamma * P_0,
C_gamma = Z_gamma * C_0,
P_gamma - C_gamma = Z_gamma * (P_0 - C_0).
~~~

The same requirement concerns a finite definable family D with a varying
definable density rho: the coefficient is the whole weighted object
(D, empty structural tuple, rho). Checking only individually named constant
weights is insufficient. These identities explain density absorption;
they are not by themselves a proof of the complete lifting kernel.

## What this repository already does

This paper uses Gamma-valued volume forms throughout. Its Section 3
definitions do not identify measured RV[0] or measured VF[0] with their
unweighted versions. A zero-degree morphism must preserve the form
pointwise: the empty determinant is one and its valuation is zero.
The native implementations retain this data, including varying weights
on finite definable supports.

The following paths were inspected directly. They are already included
in the passing, source-hash-identified Section 3–6 audits.

| Interface | Existing checked evidence |
| --- | --- |
| Measured RV objects and morphisms, every degree | [RVVolumeForms](<section 3/RVVolumeForms.lean>): the form is a field for every k, and the combined weight is the form times the product of the k structural values. At k=0 the latter product is one, so the morphism condition preserves the entire form. |
| Measured VF degree zero | [MeasuredVFZero](<section 3/MeasuredVFZero.lean>) and [GammaGroundMeasuredVFZero](<section 3/GammaGroundMeasuredVFZero.lean>): genuine definable bijections with an explicit pointwise form-preservation field. |
| Mixed products, including 0 times k and k times 0 | [MeasuredRVProducts](<section 3/MeasuredRVProducts.lean>), [MeasuredVFProducts](<section 3/MeasuredVFProducts.lean>), [GammaGroundMeasuredRVProducts](<section 3/GammaGroundMeasuredRVProducts.lean>) and [GammaGroundMeasuredVFProducts](<section 3/GammaGroundMeasuredVFProducts.lean>): both pulled-back forms are multiplied without a zero-degree exception. |
| Zero-degree measured lifting | [GammaGroundZeroMeasuredLift](<section 3/GammaGroundZeroMeasuredLift.lean>): zero_combinedWeight, the form-preserving lift functor, and its full/faithful comparison. [ZeroArityRVIsomorphismLifts](<section 6/ZeroArityRVIsomorphismLifts.lean>) checks the exact form ratio against the empty determinant in 6.31. |
| Actual value-group categories | [GammaVolumeCategories](<section 3/GammaVolumeCategories.lean>) and [GammaGroundGammaVolumeCategories](<section 3/GammaGroundGammaVolumeCategories.lean>) retain a form for every degree, including zero. These are actual Gamma categories; elsewhere a Gamma-prefixed name can instead describe the parameter base. |
| Measured RES and tensor coefficients | Measured RES is a full measured RV subcategory. [MeasuredTensorRankZero](<section 3/MeasuredTensorRankZero.lean>) absorbs the whole finite measured Gamma factor into measured RES, retaining its weight. |
| Degree-zero weights do not silently collapse | [RVZeroWeightedCount](<section 4/RVZeroWeightedCount.lean>) retains every Gamma value, and [RESWeightEmbedding](<section 4/RESWeightEmbedding.lean>) proves an injective weight group-ring map, including the stated measured reduction. |
| The new relative ideal | [VariableApertureMeasuredComparison](<section 4/VariableApertureMeasuredComparison.lean>) retains the modified base form even when its degree is zero. [RelativeAnnularQuotient](<section 4/RelativeAnnularQuotient.lean>) preserves the degree-zero subring and constructs the actual forgetful/retraction maps. |

Consequently, the checked paths above already support the weighted
degree-zero coefficients needed here. This review found no corresponding
local loss of Gamma weight in those definitions, products or zero lifts.
No manuscript definition, Lean proof body or dependency pin is changed by
this review. The existing proof receipts still apply to their pinned
source state; they do not certify compatibility with a future upstream
revision.

The intentionally volume-forgetting maps to ordinary categories or Euler
targets are different from measured isomorphisms. Their loss of volume
data is not evidence that the measured source category was unweighted.

## The consumer boundary that must be revisited

There are still exact, replaceable measured inputs in Section 3:

- YinMeasuredLiftInput and YinDegreeMeasuredLiftInput in
  [CitedMeasuredIntegral](<section 3/CitedMeasuredIntegral.lean>).
- YinGammaGroundMeasuredLiftInput and YinGammaGroundDegreeMeasuredLiftInput
  in [GammaGroundCitedMeasuredIntegral](<section 3/GammaGroundCitedMeasuredIntegral.lean>).

They specify actual Gamma-measured lifts, class formulas, surjectivity and
kernel statements. The consequences using them are conditional on these
exact inputs; they are not compiled producers from the newly corrected
upstream measured development. A source citation or theorem with a similar
name does not establish the required convention and parameter bridge.
The upstream correction makes checking this boundary especially important
at degrees zero and one, in mixed products, and for families of densities.

The ordinary input discharged for Section 5 is a different record.
[Completed18GroundLiftInput](<section 5/Completed18GroundLiftInput.lean>)
constructs OriginalBaseUnmeasuredLiftInput and
YinGammaGroundUnmeasuredLiftInput from ordinary [18] Section 6 results.
It does not claim to discharge the four measured inputs above or this
paper's new Section 7 bounded kernel. The new measured zero convention
does not by itself identify an error in that ordinary producer.

## Required compatibility work, by section

| Section | Consequence of this issue |
| --- | --- |
| 1 | Keep the Gamma-valued interpretation explicit. Recheck announced measured comparisons against the final instantiated upstream maps; do not advertise a new full RV-volume integral. |
| 2 | Preserve the empty determinant and pointwise zero-degree measure equation in any imported adapters. The current local equations already have this meaning. |
| 3 | Reconcile the four measured cited inputs with the corrected upstream Gamma-valued exports. Check source/codomain categories, finite definable zero families, exact weights, all mixed products, grading, object/class formulas and kernel statements. |
| 4 | Check the actual weighted finite-Gamma coefficient actions, measured RES inclusion and tensor/retraction squares when any shared interface changes. Unlike the two upstream projects' narrower review scope, actual Gamma/RES categories and tensor maps are in scope in this repository. The local constructions listed above already retain the weights. |
| 5 | Keep the discharged ordinary producer distinct from the measured inputs. Re-audit affected interfaces if a new pin changes the ordinary APIs or their parameter syntax; do not infer an unmeasured failure solely from the measured zero correction. |
| 6 | The local geometry, revised primitive, 6.19 and revised 6.38 are checked at the existing pins. Keep the actual zero-degree form identities in lifting and any future imported replacements. This review does not introduce a new Section 6 mathematical gap. |
| 7 | Keep the entire modified density on the degree-(k-1) factor, including k=1. Prove the degree-zero kernel case with weighted finite objects and preserve weighted coefficients in refinement and groupification. A density-twist identity alone does not prove the complete kernel or remove the independent variable-aperture obligations. |
| 8 | Check which Gamma weights the actual coefficient and realization maps preserve or intentionally forget. Do not silently replace the coefficient ring by ordinary degree-zero counting, or claim final specialization preservation before the geometric comparison is checked. |

Prefer the corrected Gamma-volume interfaces actually needed by this
paper. If an argument instead uses a full RV-valued volume theorem, taking
the valuation of its density must give the required Gamma-valued map and
commute with the lifts and products being used. RV-unit information is
intentionally lost in that passage. This paper does not need to be changed
to full RV-valued volume forms, and a general coarsening-functor framework
is not an additional project goal.

## Keep this separate from the aperture repair

Weighted degree-zero coefficients absorb volume weights. They do not
construct an original-base named RV aperture or an actual continuous VF
endpoint. Thus the upstream zero correction does not undo revised 6.11,
prove the scalar version of 6.38, or show that the old scalar ideal I equals
the new relative ideal J_var. Those would require separate mathematical
arguments. In particular, the Section 4 measured comparison must retain
both W and W_gamma, with all their forms, also in degree zero.

## Before adopting the corrected upstream revision

1. Obtain its published commit and exact signatures. Keep the present
   pins and overlays until an intentional compatibility update is made.
2. Construct the measured producers actually consumed here, or retain their
   precise conditional status. Verify weighted finite families at degree
   zero and their mixed products, not merely named weighted points.
3. Check the object/class maps, zero lift, coefficient actions and the
   applicable Gamma-volume comparison squares. Recheck degree-one kernel
   factorization without assuming the target presentation as a premise.
4. Re-run affected Sections 2–6 source/type/axiom audits after changing pins
   or adapters, then update the Section 7 dependency record. Do not treat
   the current receipts as a certificate for changed upstream definitions.

No new native migration or future-version compatibility theorem is claimed
by this source review. [The machine record](verification/upstream-weighted-zero-review.json)
identifies the inspected sources and their existing verification evidence.
