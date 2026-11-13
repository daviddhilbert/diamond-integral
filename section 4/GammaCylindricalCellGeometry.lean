import «section 4».GammaCylindricalCells

/-! Actual cylindrical cells are nonempty and their graph/interval
dimension is bounded by the ambient arity. These elementary properties
do not identify that dimension with a topological dimension invariant. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaCylindricalCellGeometry
open GammaCylindricalCells GammaCellSections GammaCellUnboundedSections
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem dimension_le {B : Base (M := M)} {n d : ℕ} {C : Set (Fin n → Values.Gamma (M := M))}
    (hc : Cell B n C d) : d ≤ n := by
  induction hc with
  | base => exact le_rfl
  | graph _ _ _ ih => exact ih.trans (Nat.le_succ _)
  | band _ _ _ _ _ ih => exact Nat.succ_le_succ ih
  | upperRay _ _ _ ih => exact Nat.succ_le_succ ih
  | lowerRay _ _ _ ih => exact Nat.succ_le_succ ih
  | line _ _ ih => exact Nat.succ_le_succ ih

theorem nonempty {B : Base (M := M)} {n d : ℕ} {C : Set (Fin n → Values.Gamma (M := M))}
    (hc : Cell B n C d) : C.Nonempty := by
  induction hc with
  | base => exact ⟨Fin.elim0, Set.mem_univ _⟩
  | @graph n d C hc T hR ih =>
    obtain ⟨y, hy⟩ := ih
    exact ⟨Fin.cons (T y) y, hy, rfl⟩
  | @band n d C hc l u hlu hR ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨x, hlx, hxu⟩ := exists_between (hlu y hy)
    exact ⟨Fin.cons x y, hy, hlx, hxu⟩
  | @upperRay n d C hc l hR ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨x, hlx⟩ := exists_gt (l y)
    exact ⟨Fin.cons x y, hy, hlx⟩
  | @lowerRay n d C hc u hR ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨x, hxu⟩ := exists_lt (u y)
    exact ⟨Fin.cons x y, hy, hxu⟩
  | @line n d C hc hR ih =>
    obtain ⟨y, hy⟩ := ih
    exact ⟨Fin.cons 1 y, hy⟩

end DiamondIntegral.Section4.GammaCylindricalCellGeometry
