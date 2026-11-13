import «section 4».GammaMeasuredProfileInvariance

/-! Actual corrected-weight profiles obey scissors on definable subsets.
This uses the constructed additive pushforward, before graded descent. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaProfileScissors
open GammaOrderLogic GammaDefinableMaps GammaWeightProfiles GammaMeasuredProfileInvariance
open GammaIndicators GammaHigherPushforward

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem profile_scissor (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ}
    (I J : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I) (hJ : GammaDefinable B J)
    (hU : GammaDefinable B (I ∪ J)) (hN : GammaDefinable B (I ∩ J))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    profile h00 hκ hs B hr hγ k (I ∪ J) hU μ hμ + profile h00 hκ hs B hr hγ k (I ∩ J) hN μ hμ =
      profile h00 hκ hs B hr hγ k I hI μ hμ + profile h00 hκ hs B hr hγ k J hJ μ hμ := by
  have h := congrArg (pushforward h00 hκ hs B hr hγ k (correctedWeight μ) (correctedWeight_graph B μ hμ))
    (indicator_scissor B I J hI hJ hU hN)
  simpa only [map_add, profile] using h

theorem profile_empty (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (hE : GammaDefinable B (∅ : Set (Fin n → Values.Gamma (M := M))))
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ) :
    profile h00 hκ hs B hr hγ k ∅ hE μ hμ = 0 := by
  have he : indicatorFamily B ∅ hE = 0 := by
    apply Subtype.ext
    funext z
    simp [indicatorFamily]
  change pushforward h00 hκ hs B hr hγ k (correctedWeight μ) (correctedWeight_graph B μ hμ)
    (indicatorFamily B ∅ hE) = 0
  rw [he, map_zero]

end DiamondIntegral.Section4.GammaProfileScissors
