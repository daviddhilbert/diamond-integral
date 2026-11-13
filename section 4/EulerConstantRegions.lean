module

public import «section 4».EulerBreakpoints

/-! An actual finite-jump function is constant across an interval with no
intrinsic breakpoints. This is proved from its canonical coefficients,
not from a general topological connectedness or cell-decomposition input. -/

set_option autoImplicit false
@[expose] public noncomputable section
open Classical
namespace DiamondIntegral.Section4.EulerFunction

variable {Γ : Type*} [LinearOrder Γ] [DenselyOrdered Γ] [NoMinOrder Γ] [NoMaxOrder Γ]
  [AddCommGroup Γ]

theorem eq_of_no_breakpoints_between (k : EulerKind) (f : EulerFunction k Γ) (x y : Γ)
    (hxy : x ≤ y) (hno : ∀ z, x ≤ z → z ≤ y → z ∉ breakpoints k f) : f x = f y := by
  let v := (coefficientEquiv k).symm f
  have hp (z : Γ) (hxz : x ≤ z) (hzy : z ≤ y) : v.2.1 z = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hz
    exact hno z hxz hzy (Finset.mem_union_left _ hz)
  have hcut (c : Γ) (hc : c ∈ v.2.2.support) : c < x ↔ c < y := by
    constructor
    · exact fun h => h.trans_le hxy
    · intro hcy
      by_contra hcx
      exact hno c (le_of_not_gt hcx) hcy.le (Finset.mem_union_right _ hc)
  have hj : jumpPrefix v.2.2 x = jumpPrefix v.2.2 y := by
    unfold jumpPrefix Finsupp.sum
    apply Finset.sum_congr rfl
    intro c hc
    by_cases h : c < x
    · simp only [h, (hcut c hc).mp h, ite_true]
    · have hn : ¬ c < y := fun hcy => h ((hcut c hc).mpr hcy)
      simp only [h, hn, ite_false]
  rw [← coefficients_eval k f x, ← coefficients_eval k f y]
  change v.1 + v.2.1 x + jumpPrefix v.2.2 x = v.1 + v.2.1 y + jumpPrefix v.2.2 y
  rw [hp x le_rfl hxy, hp y hxy le_rfl, hj]

theorem eq_on_openInterval_without_breakpoints (k : EulerKind) (f : EulerFunction k Γ)
    (a b : Γ) (hno : ∀ z, a < z → z < b → z ∉ breakpoints k f)
    (x y : Γ) (hx : a < x ∧ x < b) (hy : a < y ∧ y < b) : f x = f y := by
  rcases le_total x y with hxy | hyx
  · exact eq_of_no_breakpoints_between k f x y hxy
      (fun z hxz hzy => hno z (hx.1.trans_le hxz) (hzy.trans_lt hy.2))
  · exact (eq_of_no_breakpoints_between k f y x hyx
      (fun z hyz hzx => hno z (hy.1.trans_le hyz) (hzx.trans_lt hx.2))).symm

end DiamondIntegral.Section4.EulerFunction
