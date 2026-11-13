import «section 4».GammaMeasuredProfileInvariance
import «section 4».GammaPushforwardSupport
import «section 4».GammaBoundedFamilies

/-! Explicit bounded-support and comparison results for actual corrected
weight profiles. The bound on a definable volume form remains an explicit
premise here; its general bounded-image bridge belongs to 2.41. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundedProfiles
open GammaDefinableEuler GammaOrderLogic GammaDefinableMaps GammaWeightProfiles GammaIntegerFamilies
open GammaIndicators GammaHigherPushforward GammaMeasuredProfileInvariance GammaPushforwardSupport
open GammaBoundedFamilies GammaParameterExtension GammaBaseExtension EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem correctedWeight_bounds {n : ℕ}
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (z : Fin n → Values.Gamma (M := M)) (a b c d : Values.Gamma (M := M))
    (hz : ∀ i, a ≤ z i ∧ z i ≤ b) (hμ : c ≤ μ z ∧ μ z ≤ d) :
    c * a ^ n ≤ correctedWeight μ z ∧ correctedWeight μ z ≤ d * b ^ n := by
  have hlo : a ^ n ≤ ∏ i, z i := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin n => a) (g := z) (fun i _ => (hz i).1))
  have hhi : (∏ i, z i) ≤ b ^ n := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_le_prod (s := Finset.univ) (f := z) (g := fun _ : Fin n => b) (fun i _ => (hz i).2))
  exact ⟨mul_le_mul' hμ.1 hlo, mul_le_mul' hμ.2 hhi⟩

theorem profile_bounded (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (a b c d : Values.Gamma (M := M)) (hbox : ∀ z ∈ I, ∀ i, a ≤ z i ∧ z i ≤ b)
    (hvol : ∀ z ∈ I, c ≤ μ z ∧ μ z ≤ d) :
    IsDoublyBounded (profile h00 hκ hs B hr hγ k I hI μ hμ).val := by
  apply pushforward_bounded h00 hκ hs B hr hγ k (correctedWeight μ) (correctedWeight_graph B μ hμ)
    (indicatorFamily B I hI) (c * a ^ n) (d * b ^ n)
  intro z hz
  have hzI : z ∈ I := by
    by_contra hn
    exact hz (by simp [indicatorFamily, hn])
  exact correctedWeight_bounds μ z a b c d (hbox z hzI) (hvol z hzI)

theorem profile_changeKind (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k l : EulerKind) {n : ℕ} (I : Set (Fin n → Values.Gamma (M := M))) (hI : GammaDefinable B I)
    (μ : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hμ : MapDefinable B μ)
    (a b : Values.Gamma (M := M)) (hbox : ∀ z ∈ I, ∀ i, a ≤ z i ∧ z i ≤ b) :
    changeKind k l (profile h00 hκ hs B hr hγ k I hI μ hμ).val =
      (profile h00 hκ hs B hr hγ l I hI μ hμ).val := by
  apply eval_injective l
  funext x
  obtain ⟨v, rfl⟩ := toPaperGamma.surjective x
  change changeKind k l (pushforward h00 hκ hs B hr hγ k _ _ (indicatorFamily B I hI)).val (toPaperGamma v) =
    (pushforward h00 hκ hs B hr hγ l _ _ (indicatorFamily B I hI)).val (toPaperGamma v)
  rw [changeKind_eval, pushforward_eval, pushforward_eval]
  apply integrateAll_bounded_comparison h00 hκ hs (withGamma B (Set.range ![v])) hr
    (finite_gamma_extension_small hκ B hγ ![v]) k l n _ a b
  intro z hz i
  have hval := fibreFamily_eval B (correctedWeight μ) (correctedWeight_graph B μ hμ)
    (indicatorFamily B I hI) v z
  have hzI : z ∈ I := by
    by_contra hn
    apply hz
    rw [hval]
    simp [indicatorFamily, hn]
  exact hbox z hzI i

end DiamondIntegral.Section4.GammaBoundedProfiles
