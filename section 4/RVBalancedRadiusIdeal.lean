import «section 4».RVBalancedSpecialGradings
import «section 4».RVBalancedMapGradings
import «section 4».RVRadiusQuotient

/-! The accepted radius relations form a homogeneous ideal already in
the actual finite-Gamma-balanced bounded tensor. Its comparison image is
exactly the actual bounded RV radius ideal, and evaluation kills it. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVBalancedRadiusIdeal
open RVBalancedSpecialClasses RVBalancedGradings
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def radiusIdeal (B : Base (M := M)) : Ideal (RVBoundedBalancedTensor.Source B) :=
  Ideal.span {x | ∃ γ : Values.Gamma (M := M), ∃ hγ : γ ∈ GammaRVLifts.admissibleRadii B,
    x = radiusPreimage B γ hγ}

theorem radiusPreimage_mem_ideal (B : Base (M := M)) (γ : Values.Gamma (M := M))
    (hγ : γ ∈ GammaRVLifts.admissibleRadii B) : radiusPreimage B γ hγ ∈ radiusIdeal B :=
  Ideal.subset_span ⟨γ, hγ, rfl⟩

theorem radiusIdeal_homogeneous (B : Base (M := M)) :
    (radiusIdeal B).IsHomogeneous (boundedPiece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨γ, hγ, rfl⟩
  exact ⟨1, RVBalancedSpecialGradings.radiusPreimage_mem B γ hγ⟩

theorem comparison_map_ideal (B : Base (M := M)) :
    Ideal.map (RVBoundedBalancedTensor.comparison B).toRingHom (radiusIdeal B) = RVRadiusIdeal.radiusIdeal B := by
  rw [radiusIdeal, Ideal.map_span, RVRadiusIdeal.radiusIdeal]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨γ, hγ, rfl⟩, rfl⟩
    exact ⟨γ, hγ, comparison_radiusPreimage B γ hγ⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨radiusPreimage B γ hγ, ⟨γ, hγ, rfl⟩, comparison_radiusPreimage B γ hγ⟩

theorem radiusIdeal_le_evaluation_ker (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    radiusIdeal B ≤ RingHom.ker (RVBoundedBalancedTensor.evaluation hc h00 linear hκ hs B hr hγ hΓ k).toRingHom := by
  apply Ideal.span_le.mpr
  rintro x ⟨γ, hγ', rfl⟩
  exact evaluation_radiusPreimage hc h00 linear hκ hs B hr hγ hΓ k γ hγ'

end DiamondIntegral.Section4.RVBalancedRadiusIdeal
