import Mathlib.Data.Finset.Max

/-! Every point outside a finite ordered set lies in its whole-line,
lower-ray, upper-ray or adjacent-endpoint component. This is a pure finite
order argument; no density, topology or definability theorem is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical

namespace DiamondIntegral.Section4.FiniteOrderComponents
variable {α : Type*} [LinearOrder α]

theorem component_cover (A : Finset α) (x : α) :
    x ∈ A ∨ A = ∅ ∨
      (∃ b ∈ A, x < b ∧ ∀ c ∈ A, b ≤ c) ∨
      (∃ a ∈ A, a < x ∧ ∀ c ∈ A, c ≤ a) ∨
      (∃ a ∈ A, ∃ b ∈ A, a < x ∧ x < b ∧ ∀ c ∈ A, c ≤ a ∨ b ≤ c) := by
  by_cases hx : x ∈ A
  · exact Or.inl hx
  right
  let L := A.filter (fun a => a < x)
  let U := A.filter (fun a => x < a)
  by_cases hL : L.Nonempty
  · let a := L.max' hL
    have haL : a ∈ L := Finset.max'_mem L hL
    have ha : a ∈ A := (Finset.mem_filter.mp haL).1
    have hax : a < x := (Finset.mem_filter.mp haL).2
    by_cases hU : U.Nonempty
    · let b := U.min' hU
      have hbU : b ∈ U := Finset.min'_mem U hU
      have hb : b ∈ A := (Finset.mem_filter.mp hbU).1
      have hxb : x < b := (Finset.mem_filter.mp hbU).2
      refine Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, hax, hxb, ?_⟩))
      intro c hc
      rcases lt_or_gt_of_ne (show c ≠ x from fun he => hx (he ▸ hc)) with hcx | hxc
      · exact Or.inl (Finset.le_max' L c (Finset.mem_filter.mpr ⟨hc, hcx⟩))
      · exact Or.inr (Finset.min'_le U c (Finset.mem_filter.mpr ⟨hc, hxc⟩))
    · refine Or.inr (Or.inr (Or.inl ⟨a, ha, hax, ?_⟩))
      intro c hc
      have hcx : c < x := by
        rcases lt_trichotomy c x with h | he | h
        · exact h
        · exact (hx (he ▸ hc)).elim
        · exact (hU ⟨c, Finset.mem_filter.mpr ⟨hc, h⟩⟩).elim
      exact Finset.le_max' L c (Finset.mem_filter.mpr ⟨hc, hcx⟩)
  · by_cases hU : U.Nonempty
    · let b := U.min' hU
      have hbU : b ∈ U := Finset.min'_mem U hU
      have hb : b ∈ A := (Finset.mem_filter.mp hbU).1
      have hxb : x < b := (Finset.mem_filter.mp hbU).2
      refine Or.inr (Or.inl ⟨b, hb, hxb, ?_⟩)
      intro c hc
      have hxc : x < c := by
        rcases lt_trichotomy c x with h | he | h
        · exact (hL ⟨c, Finset.mem_filter.mpr ⟨hc, h⟩⟩).elim
        · exact (hx (he ▸ hc)).elim
        · exact h
      exact Finset.min'_le U c (Finset.mem_filter.mpr ⟨hc, hxc⟩)
    · left
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro c hc
      rcases lt_trichotomy c x with h | he | h
      · exact hL ⟨c, Finset.mem_filter.mpr ⟨hc, h⟩⟩
      · exact hx (he ▸ hc)
      · exact hU ⟨c, Finset.mem_filter.mpr ⟨hc, h⟩⟩

end DiamondIntegral.Section4.FiniteOrderComponents
