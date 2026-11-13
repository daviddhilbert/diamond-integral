import «section 4».GammaBoundedMapImage
import «section 4».GammaBoundedProfiles
import «section 4».GammaBoundedFunctions
import «section 4».GammaBoundedComparison

/-! The actual corrected-weight profile of a bounded Gamma set belongs
to the bounded function ring. The volume bound comes from the proved 2.41
bridge, with its canonical-structure premise retained explicitly. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedProfileRange
open GammaOrderLogic GammaDefinableMaps GammaWeightProfiles GammaBoundedProfiles GammaBoundedMapImage

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem profile_bounded_of_domain (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (hbox : ∃ β : Values.Gamma (M := M), ∀ u ∈ I, ∀ i, β⁻¹ ≤ u i ∧ u i ≤ β) :
    EulerFunction.IsDoublyBounded (profile h00 hκ hs B hr hγ k I hI μ hμ).val := by
  obtain ⟨β, hβ⟩ := hbox
  obtain ⟨γ, hvol⟩ := bounded_map_image hc h00 linear hκ hs B hr hγ hΓ I hI μ hμ ⟨β, hβ⟩
  exact profile_bounded h00 hκ hs B hr hγ k I hI μ hμ β⁻¹ β γ⁻¹ γ hβ hvol

def boundedProfile (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (hbox : ∃ β : Values.Gamma (M := M), ∀ u ∈ I, ∀ i, β⁻¹ ≤ u i ∧ u i ≤ β) :
    GammaBoundedFunctions.boundedBaseSubring B k :=
  ⟨(profile h00 hκ hs B hr hγ k I hI μ hμ).val,
    (profile h00 hκ hs B hr hγ k I hI μ hμ).property,
    profile_bounded_of_domain hc h00 linear hκ hs B hr hγ hΓ k I hI μ hμ hbox⟩

theorem boundedProfile_euler (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (hbox : ∃ β : Values.Gamma (M := M), ∀ u ∈ I, ∀ i, β⁻¹ ≤ u i ∧ u i ≤ β) :
    GammaBoundedFunctions.baseBoundedEuler B k (boundedProfile hc h00 linear hκ hs B hr hγ hΓ k I hI μ hμ hbox) =
      GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ k n (GammaIndicators.indicatorFamily B I hI) :=
  profile_integral h00 linear hκ hs B hr hγ hΓ k I hI μ hμ

theorem boundedProfile_changeKind (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k l : EulerKind) {n : ℕ}
    (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (hbox : ∃ β : Values.Gamma (M := M), ∀ u ∈ I, ∀ i, β⁻¹ ≤ u i ∧ u i ≤ β) :
    GammaBoundedComparison.changeBaseKind B k l (boundedProfile hc h00 linear hκ hs B hr hγ hΓ k I hI μ hμ hbox) =
      boundedProfile hc h00 linear hκ hs B hr hγ hΓ l I hI μ hμ hbox := by
  apply Subtype.ext
  obtain ⟨β, hβ⟩ := hbox
  exact profile_changeKind h00 hκ hs B hr hγ k l I hI μ hμ β⁻¹ β hβ

end DiamondIntegral.Section4.GammaBoundedProfileRange
