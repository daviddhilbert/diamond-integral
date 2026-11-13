import «section 4».GammaMeasuredProfileInvariance
import «section 4».GammaPushforwardCongruence

/-! The actual corrected-weight profile depends only on the volume form
on its domain. Definable partial volume forms therefore give unambiguous
profiles through their proved extension by paper zero. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaProfileRestrictions
open GammaOrderLogic GammaDefinableMaps GammaWeightProfiles GammaMeasuredProfileInvariance
open GammaPushforwardCongruence GammaHigherPushforward GammaIndicators

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem profile_eq_on_domain (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ ν : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hμ : MapDefinable B μ) (hν : MapDefinable B ν) (he : ∀ u ∈ I, μ u = ν u) :
    profile h00 hκ hs B hr hγ k I hI μ hμ = profile h00 hκ hs B hr hγ k I hI ν hν := by
  apply Subtype.ext
  apply pushforward_eq_on_support h00 hκ hs B hr hγ k (correctedWeight μ) (correctedWeight ν)
    (correctedWeight_graph B μ hμ) (correctedWeight_graph B ν hν) (indicatorFamily B I hI)
  intro u hu
  have huI : u ∈ I := by
    by_contra hn
    exact hu (by simp [indicatorFamily, hn])
  change μ u * (∏ i, u i) = ν u * (∏ i, u i)
  rw [he u huI]

def partialProfile (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hμ : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) |
      Fin.tail z ∈ I ∧ z 0 = μ (Fin.tail z)}) : GammaDefinableConvolution.baseSubgroup B k :=
  profile h00 hκ hs B hr hγ k I hI (extendWeight I μ) (extendWeight_definable B I hI μ hμ)

theorem partialProfile_eq_extension (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hμ : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) |
      Fin.tail z ∈ I ∧ z 0 = μ (Fin.tail z)})
    (ν : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hν : MapDefinable B ν)
    (he : ∀ u ∈ I, μ u = ν u) :
    partialProfile h00 hκ hs B hr hγ k I hI μ hμ = profile h00 hκ hs B hr hγ k I hI ν hν := by
  apply profile_eq_on_domain
  intro u hu
  simpa only [extendWeight, ite_eq_left hu] using he u hu

end DiamondIntegral.Section4.GammaProfileRestrictions
