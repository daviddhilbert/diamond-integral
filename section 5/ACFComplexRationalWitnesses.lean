import «section 5».ComplexElementaryModels
import «section 3».ACFDefinableRationalValues

/-! A unique output in an actual elementary extension of the complex
field is a rational function of its inputs with original complex
coefficients. The field, coefficient embedding and adjoin bridges are
all instantiated, rather than supplied as presentation assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language FirstOrder.Ring
attribute [local instance] ComplexModels.ringStructure ComplexModels.acfModel ComplexModels.fieldModel
  ComplexModels.fieldStructure ComplexModels.compatibleRing ComplexModels.characteristicZero
  ComplexModels.algebraicallyClosed ComplexModels.algebra

theorem complex_model_graph_rational (M : ComplexModels.Model) {n : ℕ}
    (φ : (Language.ring[[ℂ]]).Formula (Fin n ⊕ Fin 1)) (x : Fin n → M) (y : M)
    (hxy : φ.Realize (Sum.elim x (fun _ => y)))
    (hu : ∀ z : M, φ.Realize (Sum.elim x (fun _ => z)) → z = y) :
    ∃ p q : MvPolynomial (Fin n) ℂ, p.eval₂ (ComplexModels.coefficientHom M) x /
      q.eval₂ (ComplexModels.coefficientHom M) x = y ∧ q.eval₂ (ComplexModels.coefficientHom M) x ≠ 0 := by
  let F := IntermediateField.adjoin ℂ (Set.range x)
  let c : ℂ → F.toSubfield := fun a => ⟨ComplexModels.coefficientHom M a, F.algebraMap_mem a⟩
  let R : Set (Fin n ⊕ Fin 1 → M) := {v | φ.Realize v}
  let ψ : Language.ring.Formula (F.toSubfield ⊕ (Fin n ⊕ Fin 1)) :=
    (ComplexModels.coefficientFormula φ).relabel (Sum.map c id)
  have hR : (F.toSubfield : Set M).Definable Language.ring R := by
    apply Set.definable_iff_exists_formula_sum.mpr
    refine ⟨ψ, ?_⟩
    ext v
    have he : ψ.Realize (Sum.elim Subtype.val v) ↔ φ.Realize v := by
      simp only [ψ, Formula.realize_relabel]
      have hfun : Sum.elim Subtype.val v ∘ Sum.map c id = Sum.elim (ComplexModels.coefficientHom M) v := by
        funext i
        cases i <;> rfl
      rw [hfun]
      exact ComplexModels.coefficientFormula_realize M φ v
    exact he.symm
  have hy := DiamondIntegral.Section3.acf_definable_graph_value_mem_adjoin F.toSubfield R hR x y hxy hu
  have hle : IntermediateField.adjoin F.toSubfield (Set.range x) ≤ ⊥ := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro z ⟨i, rfl⟩
    apply IntermediateField.mem_bot.mpr
    exact ⟨⟨x i, IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)⟩, rfl⟩
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp (hle hy)
  have hyF : y ∈ F := ha ▸ a.property
  by_cases hz : y = 0
  · exact ⟨0, 1, by simp [hz], by simp⟩
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_range_iff ℂ x y).mp hyF
  refine ⟨p, q, hpq.symm, ?_⟩
  intro hq
  exact hz (by rw [hpq]; change p.eval₂ (ComplexModels.coefficientHom M) x / q.eval₂ (ComplexModels.coefficientHom M) x = 0; rw [hq, div_zero])

end DiamondIntegral.Section5
