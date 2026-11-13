import «section 4».GammaEulerSets
import «section 4».GammaPowerLawCells
import «section 4».EulerRationalBranches

/-! Actual unary fibre integration for a definable Gamma graph covered by
finitely many rational-affine power laws. The finite cells are constructed
after explicitly naming the coefficients in an auxiliary Gamma base. No
descent of the image function to the original base is claimed here. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaUnaryPowerPushforward
open GammaOrderLogic GammaBaseExtension GammaPowerLawCells GammaEulerSets GammaDefinableEuler EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem exists_power_law_image (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (D : Set (Values.Gamma (M := M))) (hD : GammaDefinableOverBase B D)
    (T : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin 2 → Values.Gamma (M := M) | z 0 ∈ D ∧ T (z 0) = z 1})
    {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) (c : Fin m → Values.Gamma (M := M))
    (hq : ∀ i, q i ≠ 0) (hcover : ∀ x ∈ D, ∃ i, T x ^ q i = c i * x ^ p i) :
    ∃ P : EulerFunction k (PaperGamma (M := M)),
      ∃ F : PaperGamma (M := M) → EulerFunction k (PaperGamma (M := M)),
        (∀ y x : Values.Gamma (M := M), F (toPaperGamma y) (toPaperGamma x) =
          if x ∈ D ∧ T x = y then 1 else 0) ∧
        (∀ y : Values.Gamma (M := M), P (toPaperGamma y) = totalEuler k (F (toPaperGamma y))) ∧
        totalEuler k P = eulerValue h00 B k D hD := by
  let C := fun i => lawCell D T (p i) (q i) (c i)
  let B' := withGamma B (Set.range c)
  have hC : ∀ i, GammaDefinableOverBase B' (C i) := lawCells_definable_extend B D T hT p q c
  have hPi (i : Fin m) : GammaDefinableOverBase B' (firstCell C i) := firstCell_definable B' C hC i
  let w := fun i => indicator h00 B' k (firstCell C i) (hPi i)
  have hw (i : Fin m) (x : Values.Gamma (M := M)) :
      w i (toPaperGamma x) = if x ∈ firstCell C i then 1 else 0 :=
    indicator_eval h00 B' k _ (hPi i) x
  have hex (x : Values.Gamma (M := M)) : (∃ i, x ∈ C i) ↔ x ∈ D := by
    constructor
    · rintro ⟨i, hi⟩
      exact hi.1
    · intro hx
      obtain ⟨i, hi⟩ := hcover x hx
      exact ⟨i, hx, hi⟩
  have hsum : (∑ i : Fin m, w i) = indicator h00 B k D hD := by
    apply eval_injective k
    funext z
    obtain ⟨x, rfl⟩ := toPaperGamma.surjective z
    change (∑ i : Fin m, w i) (toPaperGamma x) = indicator h00 B k D hD (toPaperGamma x)
    simp only [eval_finsetSum, hw, indicator_eval]
    simpa only [hex] using firstCell_sum C x
  have hcompat : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ x : Values.Gamma (M := M),
      w i (Additive.ofMul x) ≠ 0 → T x ^ q i = c i * x ^ p i := by
    intro i _ x hn
    change w i (toPaperGamma x) ≠ 0 at hn
    have hx : x ∈ firstCell C i := by
      by_contra hx
      exact hn (by rw [hw, ite_eq_right hx])
    exact hx.1.2
  obtain ⟨P, F, hF, hP, hEuler⟩ := exists_pushforward_of_power_laws
    (G := Values.Gamma (M := M)) k Finset.univ p q c hq T w hcompat
  refine ⟨P, F, ?_, ?_, ?_⟩
  · intro y x
    rw [hF, hsum, indicator_eval]
    rw [show Additive.toMul (toPaperGamma x) = x from rfl]
    have heq : Additive.ofMul (T x) = toPaperGamma y ↔ T x = y := toPaperGamma.injective.eq_iff
    simp only [heq]
    by_cases hy : T x = y <;> by_cases hx : x ∈ D <;> simp [hy, hx]
  · intro y
    exact hP (toPaperGamma y)
  · rw [hsum] at hEuler
    exact hEuler

end DiamondIntegral.Section4.GammaUnaryPowerPushforward
