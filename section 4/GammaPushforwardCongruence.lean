import «section 4».GammaHigherPushforward
import «section 4».GammaIntegralCongruence

/-! Actual higher-dimensional pushforward is independent of the original
base presentation when the source weight and Gamma map agree pointwise. -/

set_option autoImplicit false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaPushforwardCongruence
open GammaDefinableEuler GammaOrderLogic GammaIntegerFamilies GammaHigherPushforward
open GammaIntegralCongruence GammaParameterExtension EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem pushforward_congr (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B C : Base (M := M)) (hrB : Cardinal.mk B.real < κ) (hγB : Cardinal.mk B.gamma < κ)
    (hrC : Cardinal.mk C.real < κ) (hγC : Cardinal.mk C.gamma < κ)
    (k : EulerKind) {n : ℕ}
    (T U : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (hU : GammaDefinable C {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = U (Fin.tail z)})
    (f : familySubgroup B n) (g : familySubgroup C n)
    (hmap : ∀ z, T z = U z) (hweight : ∀ z, f.val z = g.val z) :
    (pushforward h00 hκ hs B hrB hγB k T hT f).val =
      (pushforward h00 hκ hs C hrC hγC k U hU g).val := by
  apply eval_injective k
  funext x
  obtain ⟨a, rfl⟩ := toPaperGamma.surjective x
  change (pushforward h00 hκ hs B hrB hγB k T hT f).val (toPaperGamma a) =
    (pushforward h00 hκ hs C hrC hγC k U hU g).val (toPaperGamma a)
  rw [pushforward_eval, pushforward_eval]
  apply integrateAll_congr h00 hκ hs
    (GammaBaseExtension.withGamma B (Set.range ![a])) (GammaBaseExtension.withGamma C (Set.range ![a]))
    hrB (finite_gamma_extension_small hκ B hγB ![a]) hrC (finite_gamma_extension_small hκ C hγC ![a]) k n
  intro u
  rw [fibreFamily_eval, fibreFamily_eval, hmap u, hweight u]

theorem pushforward_eq_on_support (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (k : EulerKind) {n : ℕ}
    (T U : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = T (Fin.tail z)})
    (hU : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) | z 0 = U (Fin.tail z)})
    (f : familySubgroup B n) (hmap : ∀ z, f.val z ≠ 0 → T z = U z) :
    (pushforward h00 hκ hs B hr hγ k T hT f).val = (pushforward h00 hκ hs B hr hγ k U hU f).val := by
  apply eval_injective k
  funext x
  obtain ⟨a, rfl⟩ := toPaperGamma.surjective x
  change (pushforward h00 hκ hs B hr hγ k T hT f).val (toPaperGamma a) =
    (pushforward h00 hκ hs B hr hγ k U hU f).val (toPaperGamma a)
  rw [pushforward_eval, pushforward_eval]
  apply integrateAll_congr h00 hκ hs
    (GammaBaseExtension.withGamma B (Set.range ![a])) (GammaBaseExtension.withGamma B (Set.range ![a]))
    hr (finite_gamma_extension_small hκ B hγ ![a]) hr (finite_gamma_extension_small hκ B hγ ![a]) k n
  intro u
  rw [fibreFamily_eval, fibreFamily_eval]
  by_cases hf : f.val u = 0
  · simp only [hf, ite_self]
  · rw [hmap u hf]

end DiamondIntegral.Section4.GammaPushforwardCongruence
