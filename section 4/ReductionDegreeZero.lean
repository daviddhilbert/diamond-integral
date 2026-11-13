import «section 4».PositiveIdealDegreeZero
import «section 4».RESReductionGradings
import «section 4».RVRadiusQuotient

/-! The measured RES reduction, ordinary RES fibre reduction and accepted
RV radius quotient preserve their entire degree-zero coefficient rings.
Their generators have positive degree. No RV singleton splitting or
divisibility of the RV-liftable value subgroup is used. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.ReductionDegreeZero
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem measured_ideal_le_zero_ker (B : Base (M := M)) :
    RESMeasuredReduction.reductionIdeal B ≤ RingHom.ker (RESGrading.gradingCoaction B).zeroProjection := by
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro x ⟨α, β, hα, hβ, rfl⟩
    exact (RESGrading.gradingCoaction B).zeroProjection_of_positive_mem (by decide : (1 : ℕ) ≠ 0)
      ((RESRingCoaction.gradedPiece B 1).sub_mem
        (RESRingCoaction.class_mem_gradedPiece B _) (RESRingCoaction.class_mem_gradedPiece B _))
  · apply Ideal.span_le.mpr
    rintro x (rfl : x = RESMeasuredReduction.affineClass B)
    exact (RESGrading.gradingCoaction B).zeroProjection_of_positive_mem (by decide : (1 : ℕ) ≠ 0)
      (RESReductionGradings.measured_affine_mem B)

theorem ordinary_ideal_le_zero_ker (B : Base (M := M)) :
    RESOrdinaryReduction.fibreIdeal B ≤ RingHom.ker (RESOrdinaryGrading.gradingCoaction B).zeroProjection := by
  apply Ideal.span_le.mpr
  rintro x ⟨α, hα, rfl⟩
  exact (RESOrdinaryGrading.gradingCoaction B).zeroProjection_of_positive_mem (by decide : (1 : ℕ) ≠ 0)
    ((RESOrdinaryGrading.gradedPiece B 1).sub_mem
      (RESOrdinaryGrading.class_mem B _) (RESOrdinaryGrading.class_mem B _))

theorem radius_ideal_le_zero_ker (B : Base (M := M)) :
    RVRadiusIdeal.radiusIdeal B ≤ RingHom.ker (RVBoundedGrading.gradingCoaction B).zeroProjection := by
  apply Ideal.span_le.mpr
  rintro x ⟨γ, hγ, rfl⟩
  exact (RVBoundedGrading.gradingCoaction B).zeroProjection_of_positive_mem (by decide : (1 : ℕ) ≠ 0)
    (RVRadiusIdeal.pGamma_mem_degree_one B γ hγ)

def measuredEquiv (B : Base (M := M)) :
    (RESGrading.gradingCoaction B).zeroSubring ≃+* (RESReductionGradings.measuredCoaction B).zeroSubring :=
  (RESGrading.gradingCoaction B).quotientZeroEquiv (RESMeasuredReduction.reductionIdeal B)
    (RESReductionGradings.measured_ideal_coefficients B) (measured_ideal_le_zero_ker B)

def ordinaryEquiv (B : Base (M := M)) :
    (RESOrdinaryGrading.gradingCoaction B).zeroSubring ≃+* (RESReductionGradings.ordinaryCoaction B).zeroSubring :=
  (RESOrdinaryGrading.gradingCoaction B).quotientZeroEquiv (RESOrdinaryReduction.fibreIdeal B)
    (RESReductionGradings.ordinary_ideal_coefficients B) (ordinary_ideal_le_zero_ker B)

def radiusEquiv (B : Base (M := M)) :
    RVZeroDegreeEquivalences.resZero B ≃+* (RVRadiusQuotient.coaction B).zeroSubring :=
  (RVZeroDegreeEquivalences.boundedEquiv B).trans
    ((RVBoundedGrading.gradingCoaction B).quotientZeroEquiv (RVRadiusIdeal.radiusIdeal B)
      (RVRadiusQuotient.ideal_coefficients B) (radius_ideal_le_zero_ker B))

theorem measuredEquiv_apply (B : Base (M := M)) (x : (RESGrading.gradingCoaction B).zeroSubring) :
    (measuredEquiv B x).val = RESMeasuredReduction.quotient B x.val := rfl

theorem ordinaryEquiv_apply (B : Base (M := M)) (x : (RESOrdinaryGrading.gradingCoaction B).zeroSubring) :
    (ordinaryEquiv B x).val = RESOrdinaryReduction.quotient B x.val := rfl

theorem radiusEquiv_apply (B : Base (M := M)) (x : RVZeroDegreeEquivalences.resZero B) :
    (radiusEquiv B x).val = RVRadiusQuotient.ofRES B x.val := rfl

end DiamondIntegral.Section4.ReductionDegreeZero
