import «section 4».RVOrdinaryCoefficientTranslationKernel

/-! Explicit transport interfaces for the author-approved corrected
Proposition 3.18 (T001). These are the groupified consequences of its
positive surjectivity and coefficient-translation kernel congruences.
They are hypotheses, not global axioms or assertions of tensor
injectivity. The author explicitly permits the unformalized Section 3 results to be
taken as given (November 12). These precise local interfaces therefore
serve as accepted, replaceable Section 3 inputs; their upstream formal
transport is not a blocker for Section 4. No
bounded tensor presentation is part of this interface. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.ApprovedT001Presentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure Ordinary (B : Base (M := M)) : Prop where
  surjective : Function.Surjective (RVOrdinaryBalancedTensor.comparison B)
  kernel_le : RingHom.ker (RVOrdinaryBalancedTensor.comparison B).toRingHom ≤
    RVOrdinaryCoefficientTranslationKernel.coefficientIdeal B

structure Measured (B : Base (M := M)) : Prop where
  surjective : Function.Surjective (RVFiniteBalancedTensor.comparison B)
  kernel_le : RingHom.ker (RVFiniteBalancedTensor.comparison B).toRingHom ≤
    RVCoefficientCoordinateTranslationKernel.coefficientIdeal B

theorem Ordinary.kernel_eq {B : Base (M := M)} (p : Ordinary B) :
    RingHom.ker (RVOrdinaryBalancedTensor.comparison B).toRingHom =
      RVOrdinaryCoefficientTranslationKernel.coefficientIdeal B :=
  le_antisymm p.kernel_le (RVOrdinaryCoefficientTranslationKernel.coefficientIdeal_le_comparison_ker B)

theorem Measured.kernel_eq {B : Base (M := M)} (p : Measured B) :
    RingHom.ker (RVFiniteBalancedTensor.comparison B).toRingHom =
      RVCoefficientCoordinateTranslationKernel.coefficientIdeal B :=
  le_antisymm p.kernel_le (RVCoefficientCoordinateTranslationKernel.coefficientIdeal_le_comparison_ker B)

end DiamondIntegral.Section4.ApprovedT001Presentation
