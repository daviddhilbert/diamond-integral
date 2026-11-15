import «section 5».ComplexElementaryModels

/-! Global single-valuedness of a defining graph is one actual sentence,
so it transfers from the original complex field to every model of its
elementary diagram. This discharges the uniqueness input in each model
before compactness is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language

def uniqueOutputFormula {L : Language} {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 1)) :
    L.Formula (Fin n ⊕ Fin 2) :=
  ((φ.relabel (Sum.map id (fun _ => (0 : Fin 2)))) ⊓
    (φ.relabel (Sum.map id (fun _ => (1 : Fin 2))))).imp
      ((Term.var (.inr 0) : L.Term (Fin n ⊕ Fin 2)).equal (.var (.inr 1)))

def uniqueOutputSentence {L : Language} {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 1)) : L.Sentence :=
  ((uniqueOutputFormula φ).relabel (Sum.inr : Fin n ⊕ Fin 2 → Empty ⊕ (Fin n ⊕ Fin 2))).iAlls (Fin n ⊕ Fin 2)

theorem uniqueOutputFormula_realize {L : Language} {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 1))
    (M : Type*) [L.Structure M] (v : Fin n ⊕ Fin 2 → M) :
    (uniqueOutputFormula φ).Realize v ↔
      (φ.Realize (Sum.elim (fun i => v (.inl i)) (fun _ => v (.inr 0))) ∧
        φ.Realize (Sum.elim (fun i => v (.inl i)) (fun _ => v (.inr 1)))) → v (.inr 0) = v (.inr 1) := by
  simp only [uniqueOutputFormula, Formula.realize_imp, Formula.realize_inf, Formula.realize_relabel,
    Formula.realize_equal, Term.realize_var]
  have h0 : v ∘ Sum.map id (fun _ : Fin 1 => (0 : Fin 2)) =
      Sum.elim (fun i => v (.inl i)) (fun _ => v (.inr 0)) := by funext i; cases i <;> rfl
  have h1 : v ∘ Sum.map id (fun _ : Fin 1 => (1 : Fin 2)) =
      Sum.elim (fun i => v (.inl i)) (fun _ => v (.inr 1)) := by funext i; cases i <;> rfl
  rw [h0, h1]

theorem uniqueOutputSentence_realize {L : Language} {n : ℕ} (φ : L.Formula (Fin n ⊕ Fin 1))
    (M : Type*) [L.Structure M] :
    M ⊨ uniqueOutputSentence φ ↔ ∀ (x : Fin n → M) (y z : M),
      φ.Realize (Sum.elim x (fun _ => y)) → φ.Realize (Sum.elim x (fun _ => z)) → y = z := by
  have hrow : M ⊨ uniqueOutputSentence φ ↔ ∀ v : Fin n ⊕ Fin 2 → M, (uniqueOutputFormula φ).Realize v := by
    simp only [uniqueOutputSentence, Sentence.Realize, Formula.realize_iAlls, Formula.realize_relabel,
      Function.comp_def, Sum.elim_inr]
  rw [hrow]
  simp_rw [uniqueOutputFormula_realize]
  constructor
  · intro h x y z hy hz
    let v : Fin n ⊕ Fin 2 → M := Sum.elim x ![y, z]
    have hv := h v
    change (φ.Realize (Sum.elim x (fun _ => y)) ∧ φ.Realize (Sum.elim x (fun _ => z))) → y = z at hv
    exact hv ⟨hy, hz⟩
  · intro h v hv
    exact h (fun i => v (.inl i)) (v (.inr 0)) (v (.inr 1)) hv.1 hv.2

local instance complexUniqueCoefficientRing : FirstOrder.Ring.CompatibleRing ℂ := FirstOrder.Ring.compatibleRingOfRing ℂ

theorem complex_graph_unique_in_model {n : ℕ}
    (φ : (Language.ring[[ℂ]]).Formula (Fin n ⊕ Fin 1))
    (hφ : ∀ (x : Fin n → ℂ) (y z : ℂ), φ.Realize (Sum.elim x (fun _ => y)) →
      φ.Realize (Sum.elim x (fun _ => z)) → y = z) (M : ComplexModels.Model) :
    ∀ (x : Fin n → M) (y z : M), φ.Realize (Sum.elim x (fun _ => y)) →
      φ.Realize (Sum.elim x (fun _ => z)) → y = z := by
  have hC : ℂ ⊨ uniqueOutputSentence φ := (uniqueOutputSentence_realize φ ℂ).mpr hφ
  have hM : M ⊨ uniqueOutputSentence φ := (realize_iff_of_model_completeTheory ℂ M _).mpr hC
  exact (uniqueOutputSentence_realize φ M).mp hM

end DiamondIntegral.Section5
