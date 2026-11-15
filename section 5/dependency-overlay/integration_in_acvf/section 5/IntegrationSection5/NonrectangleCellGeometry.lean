import IntegrationSection5.CellStandardExistence

/-! Every nonrectangle cell has balanced or injective graph positioning, hence an actual positioning bijection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {R : Set (VF (M := M) × VF (M := M))}
variable {f : VF (M := M) → VF (M := M)} {t : RV (M := M)}

theorem nonrectangle_cell_alternative (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (h : CellData R f t) (hRect : R ≠ first R ×ˢ second R) :
    (∃ r, IsBalanced R f r t) ∨ (t = rv (0 : VF (M := M)) ∧ Set.InjOn f (first R)) := by
  by_cases hb : ∃ r, IsBalanced R f r t
  · exact Or.inl hb
  · right
    by_cases ht : t = rv (0 : VF (M := M))
    · rcases cell_position_constant_or_injective h with hc | hi
      · exact (hRect (constant_position_rectangle h hc)).elim
      · exact ⟨ht,hi⟩
    · obtain ⟨E,hE,hRE⟩ := CellRectangles.rectangle δ hδ h ht hb
      exact (hRect (rectangle_eq_projections _ E hRE)).elim

theorem nonrectangle_position_bijective (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (h : CellData R f t) (hRect : R ≠ first R ×ˢ second R) : Set.BijOn f (first R) (second R) := by
  rcases nonrectangle_cell_alternative δ hδ h hRect with ⟨r,hr⟩ | ⟨ht,hi⟩
  · exact hr.2.2.1.bijective
  · exact zero_paradigm_position_bijective h ht hi

end IntegrationInACVF.Section5
