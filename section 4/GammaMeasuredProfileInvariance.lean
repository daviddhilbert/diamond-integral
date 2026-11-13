import «section 4».GammaWeightProfiles
import «section 4».GammaProfileBijections

/-! The manuscript's Gamma-Jacobian volume equation preserves the actual
corrected-weight profile. The group calculation and fibrewise bijection
invariance are proved before any Grothendieck-ring descent. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaMeasuredProfileInvariance
open GammaOrderLogic GammaDefinableMaps GammaWeightProfiles GammaProfileBijections GammaBijectiveRelations

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem correctedWeight_preserved {n m : ℕ}
    (I : Set (Fin m → Values.Gamma (M := M)))
    (μ : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (σ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (φ : (Fin m → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M)))
    (hvol : ∀ u ∈ I, μ u = σ (φ u) * (∏ i, φ u i) / (∏ i, u i)) :
    ∀ u ∈ I, correctedWeight μ u = correctedWeight σ (φ u) := by
  intro u hu
  change μ u * (∏ i, u i) = σ (φ u) * (∏ i, φ u i)
  rw [hvol u hu, div_mul_cancel]

theorem correctedWeight_graph (B : Base (M := M)) {n : ℕ}
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = correctedWeight μ (Fin.tail z)} := by
  have h := correctedWeight_definable B μ hμ
  unfold MapDefinable at h
  convert h using 1
  ext z
  change z 0 = correctedWeight μ (Fin.tail z) ↔ z 0 = correctedWeight μ (fun i => z i.succ)
  have he : Fin.tail z = (fun i => z i.succ) := by funext i; rfl
  rw [he]

theorem profile_volume_bijOn (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (n m : ℕ)
    (I : Set (Fin m → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (J : Set (Fin n → Values.Gamma (M := M))) (hJ : GammaDefinable B J)
    (μ : (Fin m → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (σ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hσ : MapDefinable B σ)
    (φ : (Fin m → Values.Gamma (M := M)) → (Fin n → Values.Gamma (M := M)))
    (hφ : GammaDefinable B (graphOn I φ)) (hbij : Set.BijOn φ I J)
    (hvol : ∀ u ∈ I, μ u = σ (φ u) * (∏ i, φ u i) / (∏ i, u i)) :
    profile h00 hκ hs B hr hγ k I hI μ hμ = profile h00 hκ hs B hr hγ k J hJ σ hσ := by
  exact profile_bijOn h00 linear hκ hs B hr hγ hΓ k n m I hI J hJ
    (correctedWeight μ) (correctedWeight σ) (correctedWeight_graph B μ hμ) (correctedWeight_graph B σ hσ)
    φ hφ hbij (correctedWeight_preserved I μ σ φ hvol)

end DiamondIntegral.Section4.GammaMeasuredProfileInvariance
