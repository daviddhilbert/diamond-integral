import Section3.TupleCompactness

/-! Saturation selects finitely many whole first-order witness packages.
The selected indices retain all discrete data carried by the packages;
only their fixed validity formulas are used for compactness. -/
set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Section3

theorem finite_firstOrder_witness_selection {M : Type} [LRV.Structure M]
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    {n : ℕ} (θ : LRV.BoundedFormula S n) {W : Type*}
    (valid : W → LRV.BoundedFormula S n)
    (hcover : ∀ x, θ.Realize Subtype.val x → ∃ w, (valid w).Realize Subtype.val x) :
    ∃ J : Finset W, ∀ x, θ.Realize Subtype.val x →
      ∃ w ∈ J, (valid w).Realize Subtype.val x := by
  have hc : ∀ x, θ.Realize Subtype.val x →
      ∃ ψ ∈ Set.range valid, ψ.Realize Subtype.val x := by
    intro x hx
    obtain ⟨w, hw⟩ := hcover x hx
    exact ⟨valid w, Set.mem_range_self w, hw⟩
  obtain ⟨s, hsvalid, hscov⟩ := hs.finite_subcover (Subtype.val : S → M) hsmall θ
    (Set.range valid) hc
  have he (ψ : s) : ∃ w, valid w = ψ.val := hsvalid ψ.val ψ.property
  let chooseWitness (ψ : s) : W := Classical.choose (he ψ)
  let J := s.attach.image chooseWitness
  refine ⟨J, ?_⟩
  intro x hx
  obtain ⟨ψ, hψ, hψx⟩ := hscov x hx
  refine ⟨chooseWitness ⟨ψ, hψ⟩, Finset.mem_image.mpr
    ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
  change (valid (Classical.choose (he ⟨ψ, hψ⟩))).Realize Subtype.val x
  rw [Classical.choose_spec (he ⟨ψ, hψ⟩)]
  exact hψx

end DiamondIntegral.Section5
