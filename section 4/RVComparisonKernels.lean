import «section 4».CoactionKernel
import «section 4».RVBalancedZeroDegree

/-! The actual measured, bounded and radius-quotient comparison kernels
are homogeneous and have no zero-degree component. Every kernel element
is a finite sum of positive-degree homogeneous kernel elements. The
global generators and evaluation descent are not asserted here. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVComparisonKernels
open RVBalancedGradings
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem measured_compatibility (B : Base (M := M)) :
    (Polynomial.mapRingHom (RVFiniteBalancedTensor.comparison B).toRingHom).comp (measuredCoaction B).map =
      (RVGrading.gradingCoaction B).map.comp (RVFiniteBalancedTensor.comparison B).toRingHom :=
  (measuredCoaction B).map_coaction_of_mem (RVGrading.gradingCoaction B) (RVFiniteBalancedTensor.comparison B).toRingHom
    (fun _ _ hx => (RVBalancedMapGradings.gradedMeasuredComparison B).map_mem hx)

theorem bounded_compatibility (B : Base (M := M)) :
    (Polynomial.mapRingHom (RVBoundedBalancedTensor.comparison B).toRingHom).comp (boundedCoaction B).map =
      (RVBoundedGrading.gradingCoaction B).map.comp (RVBoundedBalancedTensor.comparison B).toRingHom :=
  (boundedCoaction B).map_coaction_of_mem (RVBoundedGrading.gradingCoaction B) (RVBoundedBalancedTensor.comparison B).toRingHom
    (fun _ _ hx => (RVBalancedMapGradings.gradedBoundedComparison B).map_mem hx)

theorem radius_compatibility (B : Base (M := M)) :
    (Polynomial.mapRingHom (RVBalancedRadiusQuotient.comparison B).toRingHom).comp (RVBalancedRadiusQuotient.coaction B).map =
      (RVRadiusQuotient.coaction B).map.comp (RVBalancedRadiusQuotient.comparison B).toRingHom :=
  (RVBalancedRadiusQuotient.coaction B).map_coaction_of_mem (RVRadiusQuotient.coaction B)
    (RVBalancedRadiusQuotient.comparison B).toRingHom (fun _ _ hx => (RVBalancedRadiusQuotient.comparison B).map_mem hx)

theorem measured_kernel_homogeneous (B : Base (M := M)) :
    (RingHom.ker (RVFiniteBalancedTensor.comparison B).toRingHom).IsHomogeneous (measuredPiece B) :=
  (measuredCoaction B).kernel_homogeneous (RVGrading.gradingCoaction B) (RVFiniteBalancedTensor.comparison B).toRingHom
    (measured_compatibility B)

theorem bounded_kernel_homogeneous (B : Base (M := M)) :
    (RingHom.ker (RVBoundedBalancedTensor.comparison B).toRingHom).IsHomogeneous (boundedPiece B) :=
  (boundedCoaction B).kernel_homogeneous (RVBoundedGrading.gradingCoaction B) (RVBoundedBalancedTensor.comparison B).toRingHom
    (bounded_compatibility B)

theorem radius_kernel_homogeneous (B : Base (M := M)) :
    (RingHom.ker (RVBalancedRadiusQuotient.comparison B).toRingHom).IsHomogeneous (RVBalancedRadiusQuotient.piece B) :=
  (RVBalancedRadiusQuotient.coaction B).kernel_homogeneous (RVRadiusQuotient.coaction B)
    (RVBalancedRadiusQuotient.comparison B).toRingHom (radius_compatibility B)

theorem measured_positive_decomposition (B : Base (M := M)) (x : RVFiniteBalancedTensor.Source B)
    (hx : RVFiniteBalancedTensor.comparison B x = 0) :
    (∑ n ∈ ((measuredCoaction B).map x).support.filter (fun n => 0 < n), ((measuredCoaction B).map x).coeff n) = x :=
  (measuredCoaction B).kernel_positive_decomposition (RVGrading.gradingCoaction B)
    (RVFiniteBalancedTensor.comparison B).toRingHom (measured_compatibility B)
    (RVBalancedZeroDegree.measured_comparison_injective B) x hx

theorem bounded_positive_decomposition (B : Base (M := M)) (x : RVBoundedBalancedTensor.Source B)
    (hx : RVBoundedBalancedTensor.comparison B x = 0) :
    (∑ n ∈ ((boundedCoaction B).map x).support.filter (fun n => 0 < n), ((boundedCoaction B).map x).coeff n) = x :=
  (boundedCoaction B).kernel_positive_decomposition (RVBoundedGrading.gradingCoaction B)
    (RVBoundedBalancedTensor.comparison B).toRingHom (bounded_compatibility B)
    (RVBalancedZeroDegree.bounded_comparison_injective B) x hx

theorem radius_positive_decomposition (B : Base (M := M)) (x : RVBalancedRadiusQuotient.Ring B)
    (hx : RVBalancedRadiusQuotient.comparison B x = 0) :
    (∑ n ∈ ((RVBalancedRadiusQuotient.coaction B).map x).support.filter (fun n => 0 < n),
      ((RVBalancedRadiusQuotient.coaction B).map x).coeff n) = x :=
  (RVBalancedRadiusQuotient.coaction B).kernel_positive_decomposition (RVRadiusQuotient.coaction B)
    (RVBalancedRadiusQuotient.comparison B).toRingHom (radius_compatibility B)
    (RVBalancedZeroDegree.radius_comparison_injective B) x hx

end DiamondIntegral.Section4.RVComparisonKernels
