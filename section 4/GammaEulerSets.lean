import «section 4».GammaDefinableFunctions
import «section 4».EulerTruncation

/-! Canonical Euler values for actual unary definable Gamma sets.
Representation choices and the parameter base do not affect the value.
Scissor additivity, singleton/empty values, bounded comparison and unary
stabilization are derived from the constructed function integral. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaEulerSets
open GammaDefinableEuler GammaDefinableFunctions EulerFunction

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem exists_indicator (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (A : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A) :
    ∃ f : EulerFunction k (PaperGamma (M := M)),
      ∀ γ : Values.Gamma (M := M), f (toPaperGamma γ) = if γ ∈ A then 1 else 0 := by
  have h := integerDefinable_indicator B A hA
  obtain ⟨f, hf⟩ := exists_eulerFunction_of_definable h00 B k
    (fun x : PaperGamma (M := M) => if toPaperGamma.symm x ∈ A then 1 else 0) h.1 h.2
  exact ⟨f, fun γ => hf (toPaperGamma γ)⟩

def indicator (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (A : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A) :
    EulerFunction k (PaperGamma (M := M)) := Classical.choose (exists_indicator h00 B k A hA)

theorem indicator_eval (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (A : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A)
    (γ : Values.Gamma (M := M)) : indicator h00 B k A hA (toPaperGamma γ) = if γ ∈ A then 1 else 0 :=
  Classical.choose_spec (exists_indicator h00 B k A hA) γ

theorem indicator_base_independent (h00 : M ⊨ Axioms.ACVF00) (B C : Base (M := M)) (k : EulerKind)
    (A : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A)
    (hC : GammaDefinableOverBase C A) : indicator h00 B k A hA = indicator h00 C k A hC := by
  apply eval_injective k
  funext x
  obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
  change indicator h00 B k A hA (toPaperGamma γ) = indicator h00 C k A hC (toPaperGamma γ)
  rw [indicator_eval, indicator_eval]

theorem indicator_empty (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (hA : GammaDefinableOverBase B ∅) : indicator h00 B k ∅ hA = 0 := by
  apply eval_injective k
  funext x
  obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
  change indicator h00 B k ∅ hA (toPaperGamma γ) = (0 : EulerFunction k (PaperGamma (M := M))) (toPaperGamma γ)
  rw [indicator_eval, eval_zero, ite_eq_right (Set.notMem_empty γ)]

theorem indicator_singleton (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (a : Values.Gamma (M := M)) (ha : GammaDefinableClosureAtBase B a) :
    indicator h00 B k {a} ha = point k (toPaperGamma a) := by
  change GammaDefinableOverBase B {a} at ha
  apply eval_injective k
  funext x
  obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
  change indicator h00 B k {a} ha (toPaperGamma γ) = point k (toPaperGamma a) (toPaperGamma γ)
  rw [indicator_eval, point_eval]
  by_cases h : γ = a
  · subst γ
    simp only [Set.mem_singleton_iff, ite_true]
  · have hp : toPaperGamma γ ≠ toPaperGamma a := fun he => h (toPaperGamma.injective he)
    simp only [Set.mem_singleton_iff, h, hp, ite_false]

theorem indicator_scissor (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (A C : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A)
    (hC : GammaDefinableOverBase B C) (hU : GammaDefinableOverBase B (A ∪ C))
    (hI : GammaDefinableOverBase B (A ∩ C)) :
    indicator h00 B k (A ∪ C) hU + indicator h00 B k (A ∩ C) hI =
      indicator h00 B k A hA + indicator h00 B k C hC := by
  apply eval_injective k
  funext x
  obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
  simp only [eval_add, indicator_eval, Set.mem_union, Set.mem_inter_iff]
  by_cases ha : γ ∈ A <;> by_cases hc : γ ∈ C <;> simp [ha, hc]

def eulerValue (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (A : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A) : ℤ :=
  totalEuler k (indicator h00 B k A hA)

theorem eulerValue_base_independent (h00 : M ⊨ Axioms.ACVF00) (B C : Base (M := M)) (k : EulerKind)
    (A : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A)
    (hC : GammaDefinableOverBase C A) : eulerValue h00 B k A hA = eulerValue h00 C k A hC :=
  congrArg (totalEuler k) (indicator_base_independent h00 B C k A hA hC)

theorem eulerValue_empty (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (hA : GammaDefinableOverBase B ∅) : eulerValue h00 B k ∅ hA = 0 := by
  rw [eulerValue, indicator_empty, map_zero]

theorem eulerValue_singleton (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (a : Values.Gamma (M := M)) (ha : GammaDefinableClosureAtBase B a) :
    eulerValue h00 B k {a} ha = 1 := by
  change totalEuler k (indicator h00 B k {a} ha) = 1
  exact (congrArg (totalEuler k) (indicator_singleton h00 B k a ha)).trans
    (totalEuler_point k (toPaperGamma a))

theorem eulerValue_scissor (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k : EulerKind)
    (A C : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A)
    (hC : GammaDefinableOverBase B C) (hU : GammaDefinableOverBase B (A ∪ C))
    (hI : GammaDefinableOverBase B (A ∩ C)) :
    eulerValue h00 B k (A ∪ C) hU + eulerValue h00 B k (A ∩ C) hI =
      eulerValue h00 B k A hA + eulerValue h00 B k C hC := by
  have h := congrArg (totalEuler k) (indicator_scissor h00 B k A C hA hC hU hI)
  simpa only [map_add, eulerValue] using h

theorem indicator_changeKind (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k l : EulerKind)
    (A : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A) :
    changeKind k l (indicator h00 B k A hA) = indicator h00 B l A hA := by
  apply eval_injective l
  funext x
  obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
  change changeKind k l (indicator h00 B k A hA) (toPaperGamma γ) =
    indicator h00 B l A hA (toPaperGamma γ)
  rw [changeKind_eval, indicator_eval, indicator_eval]

theorem eulerValue_agree_of_bounded (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) (k l : EulerKind)
    (A : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A)
    (hbounded : ∃ L U, ∀ γ ∈ A, L ≤ γ ∧ γ ≤ U) :
    eulerValue h00 B k A hA = eulerValue h00 B l A hA := by
  obtain ⟨L, U, h⟩ := hbounded
  have hb : IsDoublyBounded (indicator h00 B k A hA) := by
    refine ⟨toPaperGamma L, toPaperGamma U, ?_⟩
    intro x hx
    obtain ⟨γ, rfl⟩ := toPaperGamma.surjective x
    have hγ : γ ∈ A := by
      by_contra hn
      exact hx (by rw [indicator_eval, ite_eq_right hn])
    exact h γ hγ
  have he := totalEuler_changeKind k l (indicator h00 B k A hA) hb
  rw [indicator_changeKind] at he
  exact he.symm

theorem eulerValue_stabilization (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (A : Set (Values.Gamma (M := M))) (hA : GammaDefinableOverBase B A) :
    ∃ R : PaperGamma (M := M), 0 < R ∧ ∀ r, R ≤ r →
      totalEuler EulerKind.geometric (truncate EulerKind.geometric (-r) r
        (indicator h00 B EulerKind.geometric A hA)) = eulerValue h00 B EulerKind.bounded A hA := by
  have h := boundedEuler_stabilization (indicator h00 B EulerKind.geometric A hA)
  simpa only [indicator_changeKind, eulerValue] using h

end DiamondIntegral.Section4.GammaEulerSets
