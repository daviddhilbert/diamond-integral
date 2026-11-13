import «section 4».GammaUnaryPowerPushforward

/-! Unary Euler invariance is proved for definable bijections admitting a
finite rational-affine power-law cover. The proof computes each actual
fibre as a singleton or empty; it assumes no Euler invariance theorem. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaPowerLawBijections
open GammaOrderLogic GammaEulerSets GammaDefinableEuler GammaUnaryPowerPushforward EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem power_law_bijection_invariance (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (D E : Set (Values.Gamma (M := M))) (hD : GammaDefinableOverBase B D)
    (hE : GammaDefinableOverBase B E) (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | z 0 ∈ D ∧ T (z 0) = z 1})
    (hinj : Set.InjOn T D) (hrange : T '' D = E)
    {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) (c : Fin m → Values.Gamma (M := M))
    (hq : ∀ i, q i ≠ 0) (hcover : ∀ x ∈ D, ∃ i, T x ^ q i = c i * x ^ p i) :
    eulerValue h00 B k D hD = eulerValue h00 B k E hE := by
  obtain ⟨P, F, hF, hP, hEuler⟩ := exists_power_law_image h00 B k D hD T hT p q c hq hcover
  have hchar (y : Values.Gamma (M := M)) : P (toPaperGamma y) = if y ∈ E then 1 else 0 := by
    rw [hP]
    by_cases hy : y ∈ E
    · have hyI : y ∈ T '' D := hrange.symm ▸ hy
      obtain ⟨x, hx, hxy⟩ := hyI
      have hFx : F (toPaperGamma y) = point k (toPaperGamma x) := by
        apply eval_injective k
        funext z
        obtain ⟨γ, rfl⟩ := toPaperGamma.surjective z
        change F (toPaperGamma y) (toPaperGamma γ) = point k (toPaperGamma x) (toPaperGamma γ)
        rw [hF, point_eval]
        by_cases hγ : γ = x
        · subst γ
          simp only [hx, hxy, and_self, ite_true]
        · have hn : ¬ (γ ∈ D ∧ T γ = y) := fun h => hγ (hinj h.1 hx (h.2.trans hxy.symm))
          have hp : toPaperGamma γ ≠ toPaperGamma x := fun h => hγ (toPaperGamma.injective h)
          simp only [hn, hp, ite_false]
      rw [hFx, totalEuler_point, ite_eq_left hy]
    · have hF0 : F (toPaperGamma y) = 0 := by
        apply eval_injective k
        funext z
        obtain ⟨γ, rfl⟩ := toPaperGamma.surjective z
        change F (toPaperGamma y) (toPaperGamma γ) = (0 : EulerFunction k (PaperGamma (M := M))) (toPaperGamma γ)
        have hn : ¬ (γ ∈ D ∧ T γ = y) := fun h => hy (hrange ▸ ⟨γ, h.1, h.2⟩)
        rw [hF, ite_eq_right hn, eval_zero]
      rw [hF0, map_zero, ite_eq_right hy]
  have he : P = indicator h00 B k E hE := by
    apply eval_injective k
    funext z
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective z
    change P (toPaperGamma γ) = indicator h00 B k E hE (toPaperGamma γ)
    rw [hchar, indicator_eval]
  rw [he] at hEuler
  exact hEuler.symm

end DiamondIntegral.Section4.GammaPowerLawBijections
