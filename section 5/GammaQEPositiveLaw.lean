import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Group
import Lean.Elab.Tactic.Omega

/-! Positive natural denominators for Laurent monomial equalities. -/
set_option autoImplicit false
namespace DiamondIntegral.Section5.GammaQE
variable {G : Type*} [CommGroup G]

theorem positive_power_law (c d a b : G) (p q r s : ℤ) (hqs : s < q)
    (he : c*a^p*b^q = d*a^r*b^s) :
    b ^ (q-s).toNat = (d/c)*a^(r-p) := by
  have hz : ((q-s).toNat : ℤ) = q-s := Int.toNat_of_nonneg (le_of_lt (sub_pos.mpr hqs))
  rw [← zpow_natCast,hz]
  calc
    b^(q-s) = (c*a^p*b^q)/(c*a^p*b^s) := by
      rw [mul_div_mul_left_eq_div,zpow_sub,div_eq_mul_inv]
    _ = (d*a^r*b^s)/(c*a^p*b^s) := congrArg (fun w => w/(c*a^p*b^s)) he
    _ = (d/c)*a^(r-p) := by
      rw [mul_div_mul_right_eq_div,zpow_sub]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ac_rfl

theorem positive_power_denominator (q s : ℤ) (hqs : s < q) : (q-s).toNat ≠ 0 := by
  omega

end DiamondIntegral.Section5.GammaQE
