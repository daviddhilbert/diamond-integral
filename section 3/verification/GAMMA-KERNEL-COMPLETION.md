# Gamma-valued measured kernel completion

All four measured input records have local proved producers. The interfaces
remain available for abstract consequences, but their mathematical fields no
longer need to be supplied as cited assumptions in the documented contexts.

| Record | Proved producer | Module |
| --- | --- | --- |
| `YinMeasuredLiftInput` | `completedMeasuredLiftInput` | [MeasuredCompletedOrdinaryInputs](../MeasuredCompletedOrdinaryInputs.lean) |
| `YinDegreeMeasuredLiftInput` | `completedDegreeMeasuredLiftInput` | [MeasuredCompletedOrdinaryInputs](../MeasuredCompletedOrdinaryInputs.lean) |
| `YinGammaGroundMeasuredLiftInput` | `completedGammaGroundMeasuredLiftInput` | [GammaCompletedMeasuredInputs](../GammaCompletedMeasuredInputs.lean) |
| `YinGammaGroundDegreeMeasuredLiftInput` | `completedGammaGroundDegreeMeasuredLiftInput` | [GammaMeasuredDegreeKernel](../GammaMeasuredDegreeKernel.lean) |

Each producer supplies the actual lift, its object-class formula, surjectivity
and exact kernel. The measured principal relation is the homogeneous
degree-one point equals positive cone relation, without a degree-zero unit.
The proof establishes equality in the positive semiring before groupification.

The construction retains the explicit canonical structure, ACVF(0,0),
uncountable saturation/homogeneity, small generated real/Gamma base,
nontrivial ground values and a valuation realizing the model predicate.
There is no resolved-base hypothesis and no definable Gamma-to-RV section.

## Proof route

1. Reuse the existing special-transformation and RV-density geometry, retaining
   the entire Gamma density graph and all original RV labels. Native elementary
   transformations, indexed gluing, finite partitions and coordinate exchanges
   preserve the original homogeneous principal congruence. The order-independent
   mixed contraction value is additive and invariant under full measured maps.
2. Prove its value on literal RV lifts, its vanishing on sets of smaller VF
   dimension, and its invariance under cofull restrictions. This gives a detector
   on the actual essential measured VF groupoid. See
   [GammaMixedEssentialContractionValues](../GammaMixedEssentialContractionValues.lean)
   and [GammaMonotoneContractionDetector](../GammaMonotoneContractionDetector.lean).
3. Internally use a generated coefficient context, then eliminate its definable
   names from the complete finite geometric witness. Principal equality reflects
   back to the original base. This proves
   `gammaContextMeasuredDegreeLift_positive_reverse_kernel` in
   [GammaPositiveDegreeReverseKernel](../GammaPositiveDegreeReverseKernel.lean).
   The previously proved weighted degree-zero equivalence completes every degree.
4. Construct actual product arrows and actual object-to-lift arrows. The degree
   detectors assemble into a multiplicative detector for the universal VF
   semiring. It is a left inverse of the lift modulo the principal relation;
   together with the forward inclusion this proves the exact global kernel.
   See [GammaCompletedSemiringDetector](../GammaCompletedSemiringDetector.lean).
5. For the ordinary base, add exactly the values of its VF field. These Gamma
   names are already definable over the original real base. Eliminating them
   gives inverse RV and VF comparisons, on objects, measured arrows, scissors,
   products and both quotient presentations. They commute with the literal
   measured object lift and preserve the principal relation in both directions.
   [MeasuredCompletedOrdinaryInputs](../MeasuredCompletedOrdinaryInputs.lean)
   therefore transports both exact kernels to the ordinary records.

Full Gamma forms, zero structural rows and weighted finite zero-degree families
are retained. No cancellation, injectivity of groupification, or inference from
the RV-valued kernel alone is used. HK supplied proof ideas only.

## Verification and downstream scope

[GAMMA-EXTENSION-PROGRESS.json](GAMMA-EXTENSION-PROGRESS.json) records targeted
compilation and the final integrated audit separately. The section receipts and
[weighted-zero compatibility receipt](../../verification/upstream-weighted-zero-upgrade/status.json)
record the checked sources, pins, theorem types and logical principles.

This discharges the four Section 3 measured integration records used upstream
of Section 6. It does not prove this paper's revised bounded variable-aperture
kernel in Section 7.26 or the Section 8 specialization. Revised Definition 6.11,
the Section 4 relative annular ideal and the Section 7–8 handoff remain in force.
No manuscript statement or aperture convention was changed by this proof.
