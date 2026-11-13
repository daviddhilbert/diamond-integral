import «section 4».RESAffineLocalization
import «section 4».RVOrdinaryDimensionFreeEvaluation

/-! Affine degree normalization on the actual ordinary graded RES
quotient. It is an actual map to degree-zero affine localization, with
kernel (A−1); after degree is forgotten its point value is A inverse. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RESAffineNormalization
open RESAffineLocalization
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def normalize (B : Base (M := M)) : RESOrdinaryReduction.ReducedRing B →+* Source B :=
  PointLocalizationNormalization.normalize (RESReductionGradings.ordinaryCoaction B) (affineClass B) (affine_mem B)

theorem normalize_homogeneous (B : Base (M := M)) {n : ℕ} {x : RESOrdinaryReduction.ReducedRing B}
    (hx : x ∈ RESReductionGradings.ordinaryPiece B n) : normalize B x = fraction B n x hx :=
  PointLocalizationNormalization.normalize_homogeneous (RESReductionGradings.ordinaryCoaction B)
    (affineClass B) (affine_mem B) hx

theorem normalize_affine (B : Base (M := M)) : normalize B (affineClass B) = 1 :=
  PointLocalizationNormalization.normalize_point (RESReductionGradings.ordinaryCoaction B) (affineClass B) (affine_mem B)

theorem normalize_kernel (B : Base (M := M)) : RingHom.ker (normalize B) = Ideal.span {affineClass B - 1} :=
  PointLocalizationEquivalence.normalize_kernel (RESReductionGradings.ordinaryCoaction B) (affineClass B) (affine_mem B)

def equivalence (B : Base (M := M)) :
    (RESOrdinaryReduction.ReducedRing B ⧸ Ideal.span {affineClass B - 1}) ≃+* Source B :=
  PointLocalizationEquivalence.equiv (RESReductionGradings.ordinaryCoaction B) (affineClass B) (affine_mem B)

theorem comparison_homogeneous (B : Base (M := M)) {n : ℕ} {x : RESOrdinaryReduction.ReducedRing B}
    (hx : x ∈ RESReductionGradings.ordinaryPiece B n) :
    comparison B (normalize B x) = Localization.mk (RESDimensionFreeReduction.fromGradedReduced B x)
      (⟨dimensionFreeAffine B ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (dimensionFreeAffine B)) := by
  rw [normalize_homogeneous B hx]
  exact comparison_fraction B n x hx

theorem comparison_point (B : Base (M := M)) :
    comparison B (normalize B (RESOrdinaryReduction.pointClass B)) =
      IsLocalization.Away.invSelf (dimensionFreeAffine B) := by
  have hQ : RESOrdinaryReduction.pointClass B ∈ RESReductionGradings.ordinaryPiece B 1 :=
    RESReductionGradings.ordinary_class_mem B (RESFibreObjects.point B)
  rw [comparison_homogeneous B hQ,
    RVOrdinaryDimensionFreeEvaluation.point_value_one]
  change Localization.mk 1 (⟨dimensionFreeAffine B ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (dimensionFreeAffine B)) = _
  have hd : (⟨dimensionFreeAffine B ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (dimensionFreeAffine B)) =
      ⟨dimensionFreeAffine B, Submonoid.mem_powers _⟩ := Subtype.ext (pow_one _)
  rw [hd, Localization.mk_eq_mk'_apply]
  rfl

end DiamondIntegral.Section4.RESAffineNormalization
