import «section 4».RVAffineTensorEvaluation

/-! Specializing the dimension-free affine class to one after affine
degree normalization recovers the ordinary target specialization on the
whole ring, including mixed-degree elements. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESAffineSpecialization
open RESAffineLocalization
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem affine_one (B : Base (M := M)) :
    RVOrdinaryDimensionFreeEvaluation.geometricQuotient B (dimensionFreeAffine B) = 1 := by
  change RVOrdinaryDimensionFreeEvaluation.geometricQuotient B (RVOrdinaryDimensionFreeEvaluation.affineClass B) = 1
  rw [RVOrdinaryDimensionFreeEvaluation.affineClass_eq, map_add,
    RVOrdinaryDimensionFreeEvaluation.geometric_torus_zero, map_one, zero_add]

def specialize (B : Base (M := M)) : Target B →+* RVOrdinaryDimensionFreeEvaluation.GeometricRing B :=
  IsLocalization.Away.lift (dimensionFreeAffine B) (g := RVOrdinaryDimensionFreeEvaluation.geometricQuotient B)
    (by rw [affine_one]; exact isUnit_one)

theorem specialize_algebraMap (B : Base (M := M)) (x : RESDimensionFreeReduction.Ring B) :
    specialize B (algebraMap (RESDimensionFreeReduction.Ring B) (Target B) x) =
      RVOrdinaryDimensionFreeEvaluation.geometricQuotient B x :=
  IsLocalization.Away.lift_eq (dimensionFreeAffine B) _ x

theorem specialize_fraction (B : Base (M := M)) (n : ℕ) (x : RESDimensionFreeReduction.Ring B) :
    specialize B (Localization.mk x
      (⟨dimensionFreeAffine B ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (dimensionFreeAffine B))) =
      RVOrdinaryDimensionFreeEvaluation.geometricQuotient B x := by
  rw [Localization.mk_eq_mk'_apply]
  have he := congrArg (specialize B) (IsLocalization.mk'_spec (Target B) x
    (⟨dimensionFreeAffine B ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (dimensionFreeAffine B)))
  rw [map_mul, specialize_algebraMap, specialize_algebraMap, map_pow, affine_one, one_pow, mul_one] at he
  exact he

theorem specialize_homogeneous (B : Base (M := M)) {n : ℕ} {x : RESOrdinaryReduction.ReducedRing B}
    (hx : x ∈ RESReductionGradings.ordinaryPiece B n) :
    specialize B (comparison B (RESAffineNormalization.normalize B x)) =
      RVOrdinaryDimensionFreeEvaluation.geometricQuotient B (RESDimensionFreeReduction.fromGradedReduced B x) := by
  rw [RESAffineNormalization.comparison_homogeneous B hx, specialize_fraction]

theorem specialize_normalize (B : Base (M := M)) (x : RESOrdinaryReduction.ReducedRing B) :
    specialize B (comparison B (RESAffineNormalization.normalize B x)) =
      RVOrdinaryDimensionFreeEvaluation.geometricQuotient B (RESDimensionFreeReduction.fromGradedReduced B x) := by
  rw [← (RESReductionGradings.ordinaryCoaction B).sum_coefficients x]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact specialize_homogeneous B ((RESReductionGradings.ordinaryCoaction B).coefficient_mem x n)

theorem tensor_specialization (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (x : RVFiniteBalancedTensor.Source B) :
    specialize B (RVAffineTensorEvaluation.geometricEvaluation h00 linear hκ hs B hr hγ hΓ x) =
      RVOrdinaryDimensionFreeEvaluation.geometricEvaluation h00 linear hκ hs B hr hγ hΓ x :=
  specialize_normalize B (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric x)

theorem quotient_specialization (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (x : RVFiniteBalancedTensor.Source B) :
    specialize B (RVAffineTensorEvaluation.geometricQuotient h00 linear hκ hs B hr hγ hΓ
      (RVAffineTensorEvaluation.quotient B x)) =
        RVOrdinaryDimensionFreeEvaluation.geometricEvaluation h00 linear hκ hs B hr hγ hΓ x :=
  tensor_specialization h00 linear hκ hs B hr hγ hΓ x

end DiamondIntegral.Section4.RESAffineSpecialization
