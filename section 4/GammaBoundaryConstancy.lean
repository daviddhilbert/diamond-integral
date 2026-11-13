import «section 4».GammaWeightedBoundary
import «section 4».GammaIndicators
import «section 4».EulerConstantRegions

/-! A definable unary Gamma fibre has constant membership between its
intrinsic boundary points. The proof uses its actual finite-jump function,
so no topological connectedness or cell-decomposition theorem is assumed.
This supplies the semantic interval step for cylindrical decomposition. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaBoundaryConstancy
open GammaOrderLogic GammaIndicators GammaWeightedFamilies GammaFamilyIntegration GammaDefinableEuler EulerFunction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M)) {n : ℕ}
variable (R : Set (Fin (n + 1) → Values.Gamma (M := M))) (hR : GammaDefinable B R)
include h00 hR

theorem boundary_breakpoints (y : Fin n → Values.Gamma (M := M)) (x : Values.Gamma (M := M)) :
    Fin.cons x y ∈ GammaFamilyBoundary.Boundary R ↔
      toPaperGamma x ∈ breakpoints EulerKind.geometric
        (fibreFunction h00 B EulerKind.geometric (fun z => if z ∈ R then (1 : ℤ) else 0)
          (indicator_definable B R hR) y) := by
  rw [mem_breakpoints_iff]
  have he : ConstantNear
      (fibreFunction h00 B EulerKind.geometric (fun z => if z ∈ R then (1 : ℤ) else 0)
        (indicator_definable B R hR) y) (toPaperGamma x) ↔
      ConstantNear (fun t : Values.Gamma (M := M) => if Fin.cons t y ∈ R then (1 : ℤ) else 0) x := by
    change (∃ l u : Values.Gamma (M := M), l < x ∧ x < u ∧ ∀ t, l < t → t < u →
      fibreFunction h00 B EulerKind.geometric (fun z => if z ∈ R then (1 : ℤ) else 0)
        (indicator_definable B R hR) y (toPaperGamma t) =
      fibreFunction h00 B EulerKind.geometric (fun z => if z ∈ R then (1 : ℤ) else 0)
        (indicator_definable B R hR) y (toPaperGamma x)) ↔ _
    simp only [fibreFunction_eval]
    rfl
  exact (GammaFamilyBoundary.boundary_iff_nonConstantNear R y x).trans (not_congr he).symm

theorem mem_iff_of_no_boundary_between (y : Fin n → Values.Gamma (M := M))
    (x z : Values.Gamma (M := M)) (hxz : x ≤ z)
    (hno : ∀ t, x ≤ t → t ≤ z → Fin.cons t y ∉ GammaFamilyBoundary.Boundary R) :
    Fin.cons x y ∈ R ↔ Fin.cons z y ∈ R := by
  let F := fibreFunction h00 B EulerKind.geometric (fun w => if w ∈ R then (1 : ℤ) else 0)
    (indicator_definable B R hR) y
  have he := eq_of_no_breakpoints_between EulerKind.geometric F (toPaperGamma x) (toPaperGamma z) hxz (by
    intro t hxt htz
    obtain ⟨a, rfl⟩ := toPaperGamma.surjective t
    exact fun ha => hno a hxt htz ((boundary_breakpoints h00 B R hR y a).mpr ha))
  have hv : (if Fin.cons x y ∈ R then (1 : ℤ) else 0) = (if Fin.cons z y ∈ R then 1 else 0) := by
    simpa only [F, fibreFunction_eval] using he
  constructor
  · intro hx
    by_contra hz
    simp only [hx, hz, ite_true, ite_false] at hv
    omega
  · intro hz
    by_contra hx
    simp only [hx, hz, ite_true, ite_false] at hv
    omega

theorem mem_iff_on_open_interval (y : Fin n → Values.Gamma (M := M))
    (a b : Values.Gamma (M := M))
    (hno : ∀ t, a < t → t < b → Fin.cons t y ∉ GammaFamilyBoundary.Boundary R)
    (x z : Values.Gamma (M := M)) (hx : a < x ∧ x < b) (hz : a < z ∧ z < b) :
    Fin.cons x y ∈ R ↔ Fin.cons z y ∈ R := by
  rcases le_total x z with hxz | hzx
  · exact mem_iff_of_no_boundary_between h00 B R hR y x z hxz
      (fun t hxt htz => hno t (hx.1.trans_le hxt) (htz.trans_lt hz.2))
  · exact (mem_iff_of_no_boundary_between h00 B R hR y z x hzx
      (fun t hzt htx => hno t (hz.1.trans_le hzt) (htx.trans_lt hx.2))).symm

end DiamondIntegral.Section4.GammaBoundaryConstancy
