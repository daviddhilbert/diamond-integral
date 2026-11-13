import Mathlib.RingTheory.Congruence.Basic
set_option autoImplicit false
namespace DiamondIntegral.Section3
universe u
variable {R : Type u} [CommSemiring R]

/-- Collapse one region while preserving equality everywhere outside it.
The region absorbs addition and multiplication by nonzero elements. -/
def regionCollapseCongruence (U : Set R) (hzero : (0 : R) ∉ U)
    (hadd : ∀ a ∈ U, ∀ b, a + b ∈ U)
    (hmul : ∀ a ∈ U, ∀ b, b ≠ 0 → a * b ∈ U) : RingCon R where
  r a b := a = b ∨ a ∈ U ∧ b ∈ U
  iseqv := ⟨fun _ => Or.inl rfl, fun h => h.elim (fun e => Or.inl e.symm)
    (fun h => Or.inr ⟨h.2,h.1⟩), by
      intro a b c hab hbc
      rcases hab with rfl | ⟨ha,hb⟩
      · exact hbc
      · rcases hbc with rfl | ⟨_,hc⟩
        · exact Or.inr ⟨ha,hb⟩
        · exact Or.inr ⟨ha,hc⟩⟩
  add' := by
    intro a b c d hab hcd
    rcases hab with rfl | ⟨ha,hb⟩
    · rcases hcd with rfl | ⟨hc,hd⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨by simpa only [add_comm] using hadd c hc a,
          by simpa only [add_comm] using hadd d hd a⟩
    · exact Or.inr ⟨hadd a ha c,hadd b hb d⟩
  mul' := by
    intro a b c d hab hcd
    rcases hab with rfl | ⟨ha,hb⟩
    · rcases hcd with rfl | ⟨hc,hd⟩
      · exact Or.inl rfl
      · by_cases h : a = 0
        · exact Or.inl (by simp only [h,zero_mul])
        · exact Or.inr ⟨by simpa only [mul_comm] using hmul c hc a h,
            by simpa only [mul_comm] using hmul d hd a h⟩
    · rcases hcd with rfl | ⟨hc,hd⟩
      · by_cases h : c = 0
        · exact Or.inl (by simp only [h,mul_zero])
        · exact Or.inr ⟨hmul a ha c h,hmul b hb c h⟩
      · have hc0 : c ≠ 0 := fun h => hzero (h ▸ hc)
        have hd0 : d ≠ 0 := fun h => hzero (h ▸ hd)
        exact Or.inr ⟨hmul a ha c hc0,hmul b hb d hd0⟩

theorem regionCollapseCongruence_eq_outside (U : Set R) (hzero : (0 : R) ∉ U)
    (hadd : ∀ a ∈ U, ∀ b, a + b ∈ U)
    (hmul : ∀ a ∈ U, ∀ b, b ≠ 0 → a * b ∈ U)
    {a b : R} (ha : a ∉ U) :
    regionCollapseCongruence U hzero hadd hmul a b ↔ a = b := by
  constructor
  · intro h
    exact h.elim id (fun h => False.elim (ha h.1))
  · exact Or.inl

/-- Relations supported in the absorbing region cannot identify two
distinct elements outside it. No additive cancellation is assumed. -/
theorem ringConGen_eq_outside_region (U : Set R) (hzero : (0 : R) ∉ U)
    (hadd : ∀ a ∈ U, ∀ b, a + b ∈ U)
    (hmul : ∀ a ∈ U, ∀ b, b ≠ 0 → a * b ∈ U)
    (r : R → R → Prop)
    (hr : ∀ a b, r a b → a = b ∨ a ∈ U ∧ b ∈ U)
    {a b : R} (ha : a ∉ U) (hab : ringConGen r a b) : a = b := by
  have hle : ringConGen r ≤ regionCollapseCongruence U hzero hadd hmul :=
    RingCon.ringConGen_le.mpr hr
  exact (regionCollapseCongruence_eq_outside U hzero hadd hmul ha).mp (hle hab)
end DiamondIntegral.Section3
