# Section 3 reuse survey

Session date: November 10, 2026 (author's local date).

## Pinned source inspection

Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`,
ACVF-QE `939346b0a99899e22a873479364e3cc5d142731c`, and
Special Transformations `9cc9760892092dd34cfad4a6dee655843c52f30c`.
The latter retains the 30-file approved finite-open-radius patch recorded
by §2. No dependency revisions were upgraded for this section.

Inspected local files and actual definitions before implementation:

| Source | Decision |
| --- | --- |
| Mathlib `GroupTheory/MonoidLocalization/GrothendieckGroup.lean` | Reuse actual additive groupification and universal property; no cancellation assumption. |
| Companion `Section4/PositiveAdditivePresentation.lean` | Reuse positive scissor presentations rather than rebuilding the free commutative monoid quotient. |
| Companion `Section4/Imported/GrothendieckRing.lean` | Reuse the existing attributed Tau Ceti extension of Mathlib groupification. Its ring universal property is included in the axiom audit; concrete section 3 products remain open. Copyright and Apache attribution stay in the imported source. |
| Mathlib `GroupTheory/Congruence/Basic.lean` | Reuse first isomorphism theorem; keep both geometric premises visible in `integralFromKernel`. |
| Companion `Section4/DefinableGeometry.lean`, `DefinableCategory.lean`, `FiniteMaps.lean`, `RealPresentations.lean` | Reuse genuine complete original-base graphs, inverse maps and real presentations. |
| Companion `Section4/RVCategories.lean` | Its ambient category permits zero target coordinates and extra morphisms. Use a proved data bridge for object lifting; define this paper's nonzero finite-target groupoid explicitly. |
| Companion `Section4/RVFibreDimension.lean`, `RVFibreInvariance.lean` | Promising Lemma 3.3 candidate. Its natural-valued empty-set convention and raw target coordinates require a bridge to this project's §2 conventions. Not a completed reuse claim yet. |
| Companion `Section4/CanonicalLift.lean` | Reuse actual RV-labelled definable object lift and finite-fibre proof. Prove VF[k] membership using this project's coordinate-interior dimension. |
| Companion `Section7/PositiveLift.lean` | Its class lift explicitly requires `VFGammaGeneratedBase`, saturation and small real base. Confirms the need to distinguish object lift from class descent. Concrete §3 graded source/target comparison remains. |
| This project `section 2/Conventions.lean`, `Dimension.lean`, `GammaJacobian.lean` | Reuse the single zero RV point, approved bottom dimension, finite Gamma values and the actual Gamma Jacobian ratio. |

## Current upstream comparison

Read-only clone `/workspace/scratch/special-transformations-latest`, HEAD
`f76d100e07c0a791259244fc7fdf06f4dfaaf8ae`.
Inspected `Section10/MeasuredRVCategory.lean`, `EssentialVFGerms.lean`,
the section README and module list. These are newer than the pinned version.
Their RV measure convention uses an RV co-small locus; this manuscript's
Definition 3.12 is pointwise everywhere. Consequently the newer headline
is not imported as if it were the same theorem. The combined-weight proof
here follows directly from this project's Gamma Jacobian definition.
The clone has not been freshly built in this session and is only source
comparison evidence. No files were copied from it into the project.

## Cited-result and search boundary

Recovered the author instructions from the `section 2` chat and the checked
project records. [18] and [19]–[22] may be replaceable explicit mathematical
inputs under their actual contexts. Do not search for missing [18] exports
or duplicate the ongoing upstream formalization. No custom global logical
premise is introduced here.

Focused local searches covered Grothendieck/groupification, congruence
quotients, finite fibres, RV/VF categories, lifting and measured categories.
Existing matching sources sufficed for this first implementation. No claim
is made to an exhaustive survey of all external registries or to absence
of a formalization of the remaining HK kernels. A focused external search
and exact scope review are still needed before rebuilding those major
prerequisites. The unchanged project plan's instruction to locate [18]'s
checkout is superseded by the later author instruction above.

## Verification

Fresh compilation and complete-type/principle evidence for actual reused
headlines are in `verification/VERIFICATION.json` and `headline-audit.txt`.
Source inspection and older upstream verification records alone are not
treated as compiler verification here. Explicit surjectivity, kernel,
parameter and topology premises remain separately visible in the receipt.
