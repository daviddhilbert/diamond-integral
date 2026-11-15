import «section 5».ElementaryNamedDefinableSets

/-! Nonempty actual definable sets over the original named parameters
contain a tuple from the elementary submodel. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
variable {L : Language} {M N P : Type} [L.Structure M] [L.Structure N]
variable (e : M ↪ₑ[L] N) (c : P → M) {n : ℕ}

theorem elementary_namedFormula_nonempty (φ : L.Formula (P ⊕ Fin n)) :
    (namedFormulaSet (e ∘ c) φ).Nonempty ↔ (namedFormulaSet c φ).Nonempty := by
  simpa only [Formula.realize_iExs,namedFormulaSet,Set.mem_setOf_eq,Set.nonempty_def] using
    e.map_formula (φ.iExs (Fin n)) c

theorem elementary_actual_nonempty (D : L.DefinableSet (Set.range (e ∘ c)) (Fin n)) :
    D.val.Nonempty ↔ (elementaryActualDefinableEquiv e c D).val.Nonempty := by
  let T := (namedActualDefinableEquiv (e ∘ c)).symm D
  obtain ⟨φ,hφ⟩ := T.property
  have hd : D.val = namedFormulaSet (e ∘ c) φ := hφ
  have hs : (elementaryActualDefinableEquiv e c D).val = namedFormulaSet c φ := by
    ext x
    change e ∘ x ∈ D.val ↔ x ∈ namedFormulaSet c φ
    rw [hd,elementary_namedFormula_mem]
  rw [hd,hs]
  exact elementary_namedFormula_nonempty e c φ

end DiamondIntegral.Section5
