import «section 4».GammaHigherPushforward
import «section 4».EulerBoundedSupport

/-! The support of actual weighted pushforward lies in the image of the
source support. A bounded corrected-weight image therefore yields an
actual bounded Euler function. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaPushforwardSupport
open GammaDefinableEuler GammaOrderLogic GammaIntegerFamilies GammaHigherPushforward
open GammaParameterExtension GammaIteratedIntegral GammaBaseExtension EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem pushforward_support (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) (a : Values.Gamma (M := M))
    (ha : (pushforward h00 hκ hs B hr hγ k T hT f).val (toPaperGamma a) ≠ 0) :
    ∃ u, f.val u ≠ 0 ∧ T u = a := by
  by_contra hn
  have he : fibreFamily B T hT f a = 0 := by
    apply Subtype.ext
    funext u
    change (fibreFamily B T hT f a).val u = 0
    rw [fibreFamily_eval]
    by_cases ht : T u = a
    · have hf : f.val u = 0 := by
        by_contra hnon
        exact hn ⟨u, hnon, ht⟩
      simp only [ht, ite_true, hf]
    · exact ite_eq_right ht
  apply ha
  rw [pushforward_eval, he, map_zero]

theorem pushforward_bounded (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ} (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (f : familySubgroup B n) (a b : Values.Gamma (M := M))
    (hbound : ∀ u, f.val u ≠ 0 → a ≤ T u ∧ T u ≤ b) :
    IsDoublyBounded (pushforward h00 hκ hs B hr hγ k T hT f).val := by
  refine ⟨toPaperGamma a, toPaperGamma b, ?_⟩
  intro x hx
  obtain ⟨c, rfl⟩ := toPaperGamma.surjective x
  obtain ⟨u, hu, he⟩ := pushforward_support h00 hκ hs B hr hγ k T hT f c hx
  change a ≤ c ∧ c ≤ b
  simpa only [he] using hbound u hu

end DiamondIntegral.Section4.GammaPushforwardSupport
