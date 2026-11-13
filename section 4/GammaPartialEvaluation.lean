import «section 4».GammaIntegerFamilies

/-! Evaluate an integer family along an original-base definable partial
Gamma graph, extending the resulting weight by zero off its domain.
Finite range and all level-set definitions preserve the original base. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaPartialEvaluation
open GammaOrderLogic GammaFamilyIntegration

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def restrictedValue {n : ℕ} (D : Set (Fin n → Values.Gamma (M := M)))
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ)
    (y : Fin n → Values.Gamma (M := M)) : ℤ := if y ∈ D then f (Fin.cons (T y) y) else 0

theorem restrictedValue_definable (B : Base (M := M)) {n : ℕ}
    (D : Set (Fin n → Values.Gamma (M := M))) (hD : GammaDefinable B D)
    (T : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M))
    (hT : GammaDefinable B {z : Fin (n + 1) → Values.Gamma (M := M) |
      (fun j => z j.succ) ∈ D ∧ T (fun j => z j.succ) = z 0})
    (f : (Fin (n + 1) → Values.Gamma (M := M)) → ℤ) (hf : IntegerFamilyDefinable B f) :
    IntegerFamilyDefinable B (restrictedValue D T f) := by
  have hV (m : ℤ) : GammaDefinable B
      {y : Fin n → Values.Gamma (M := M) | y ∈ D ∧ f (Fin.cons (T y) y) = m} := by
    have h := GammaRelationLogic.exists_definable_base B _
      (GammaRelationLogic.inter_definable_base B _ _ hT (hf.2 m))
    convert h using 1
    ext y
    change (y ∈ D ∧ f (Fin.cons (T y) y) = m) ↔
      ∃ x, (y ∈ D ∧ T y = x) ∧ f (Fin.cons x y) = m
    constructor
    · rintro ⟨hy, he⟩
      exact ⟨T y, ⟨hy, rfl⟩, he⟩
    · rintro ⟨x, ⟨hy, rfl⟩, he⟩
      exact ⟨hy, he⟩
  refine ⟨(hf.1.union (Set.finite_singleton 0)).subset ?_, ?_⟩
  · rintro m ⟨y, rfl⟩
    by_cases hy : y ∈ D
    · exact Or.inl (by rw [restrictedValue, ite_eq_left hy]; exact ⟨Fin.cons (T y) y, rfl⟩)
    · exact Or.inr (by rw [restrictedValue, ite_eq_right hy]; rfl)
  · intro m
    by_cases hm : m = 0
    · subst m
      have h := GammaQuantifierLogic.union_definable_base B _ _ (hV 0)
        (GammaRelationLogic.complement_definable_base B D hD)
      convert h using 1
      ext y
      by_cases hy : y ∈ D <;> simp [restrictedValue, hy]
    · convert hV m using 1
      ext y
      by_cases hy : y ∈ D <;> simp [restrictedValue, hy, Ne.symm hm]

end DiamondIntegral.Section4.GammaPartialEvaluation
