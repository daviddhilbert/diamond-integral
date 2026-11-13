import Section3.RVOperations
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Different outer values force a residue-scaled equality to vanish on
both sides. This is the value-cell split for a guarded RV equality. -/
theorem residue_scaled_equality_distinct_values
    (a b x y : CanonicalRV.RVSort M) (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : ValuedModelMap.inK x) (hy : ValuedModelMap.inK y)
    (hval : RVOperations.absoluteHom a ≠ RVOperations.absoluteHom b) :
    a * x = b * y ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro he
    by_cases hx0 : x = 0
    · refine ⟨hx0,?_⟩
      rw [hx0,mul_zero] at he
      exact (mul_eq_zero.mp he.symm).resolve_left hb
    · have hy0 : y ≠ 0 := by
        intro hy0
        rw [hy0,mul_zero] at he
        exact (mul_ne_zero ha hx0) he
      have hxv := ((RVOperations.inK_iff x).mp hx).resolve_left hx0
      have hyv := ((RVOperations.inK_iff y).mp hy).resolve_left hy0
      have hv := congrArg RVOperations.absoluteHom he
      rw [map_mul,map_mul,hxv,hyv,mul_one,mul_one] at hv
      exact (hval hv).elim
  · rintro ⟨rfl,rfl⟩
    simp only [mul_zero]

/-- Same-outer scalar cancellation keeps the residue factor explicit. -/
theorem residue_scaled_equality_ratio (a b x y : CanonicalRV.RVSort M)
    (ha : a ≠ 0) :
    a * x = b * y ↔ x = (b / a) * y := by
  rw [div_mul_eq_mul_div,eq_div_iff ha]
  exact ⟨fun h => (mul_comm x a).trans h,fun h => (mul_comm a x).trans h⟩

theorem residue_ratio_of_equal_values (a b : CanonicalRV.RVSort M) (ha : a ≠ 0)
    (he : RVOperations.absoluteHom a = RVOperations.absoluteHom b) :
    ValuedModelMap.inK (b / a) := by
  apply (RVOperations.inK_iff _).mpr
  right
  rw [map_div₀,← he]
  exact div_self (fun h => ha ((RVOperations.absolute_eq_zero a).mp h))
end DiamondIntegral.Section3
