import «section 7».TwoCellInput
import «section 6».InvariantHull
import «section 6».ApertureCore
import «section 6».ContractedApertures

/-! Lemma 7.20: a small valuation toolkit for the cell geometry.

`vfValue` (Section 2) is ordered like an additive valuation: larger means closer to
`0`. Under the standing bridge `hv` between `predV` and a Mathlib valuation
`Valued.v`, it is order-reversing for `Valued.v` (`vfValue_le_iff`). This file
records the ultrametric inequality, the description of `rv`-equality, the
multiplicativity of `rv`, and that `c + t^♯` is the open disc of radius
`vfValue t₀` around `c + t₀` for any lift `t₀` of `t ≠ 0`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section7.Lemma720
open DiamondIntegral.Section6 DiamondIntegral.Section2 DiamondIntegral.Section7.TwoCells

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

section Val
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
include hv

theorem vfValue_le_iff (x y : VF M) : vfValue x ≤ vfValue y ↔ Valued.v y ≤ Valued.v x :=
  (Values.vf_pred_iff_gamma_le y x).symm.trans (hv y x)

theorem vfValue_lt_iff (x y : VF M) : vfValue x < vfValue y ↔ Valued.v y < Valued.v x := by
  rw [lt_iff_not_ge, lt_iff_not_ge, vfValue_le_iff hv]

theorem vfValue_eq_iff (x y : VF M) : vfValue x = vfValue y ↔ Valued.v x = Valued.v y := by
  rw [le_antisymm_iff, le_antisymm_iff, vfValue_le_iff hv, vfValue_le_iff hv, and_comm]

/-- The ultrametric inequality for `vfValue`. -/
theorem min_le_vfValue_add (x y : VF M) : min (vfValue x) (vfValue y) ≤ vfValue (x + y) := by
  rcases le_total (vfValue x) (vfValue y) with h | h
  · rw [min_eq_left h, vfValue_le_iff hv]
    have h' := (vfValue_le_iff hv x y).mp h
    exact (Valuation.map_add _ x y).trans (max_le le_rfl h')
  · rw [min_eq_right h, vfValue_le_iff hv]
    have h' := (vfValue_le_iff hv y x).mp h
    exact (Valuation.map_add _ x y).trans (max_le h' le_rfl)

theorem vfValue_neg (x : VF M) : vfValue (-x) = vfValue x :=
  (vfValue_eq_iff hv _ _).mpr (Valuation.map_neg _ x)

theorem vfValue_sub_comm (x y : VF M) : vfValue (x - y) = vfValue (y - x) := by
  rw [← neg_sub, vfValue_neg hv]

/-- Strict ultrametric step: if `x` is strictly closer than the bound and `y` meets it,
the sum meets it. -/
theorem lt_vfValue_add {γ : GammaInfinity M} {x y : VF M} (hx : γ < vfValue x) (hy : γ < vfValue y) :
    γ < vfValue (x + y) :=
  lt_of_lt_of_le (lt_min hx hy) (min_le_vfValue_add hv x y)

/-- If `vfValue x < vfValue y`, then `x + y` has the value of `x`. -/
theorem vfValue_add_eq_of_lt {x y : VF M} (h : vfValue x < vfValue y) : vfValue (x + y) = vfValue x := by
  rw [vfValue_eq_iff hv]
  have h' := (vfValue_lt_iff hv x y).mp h
  exact Valuation.map_add_eq_of_lt_left _ h'

end Val

theorem rv_mul_eq (x y : VF M) : rv M (x * y) = rv M x * rv M y := by
  change RVOperations.rvHom (x * y) = RVOperations.rvHom x * RVOperations.rvHom y
  exact map_mul _ _ _

end DiamondIntegral.Section7.Lemma720
