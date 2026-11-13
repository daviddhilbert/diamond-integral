module

public import «section 4».PolynomialDiagonal
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-! A polynomial coaction with the diagonal identity supplies an actual
natural-number grading, including finite decomposition and uniqueness. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Classical DirectSum

namespace DiamondIntegral.Section4.PolynomialCoactionGrading

variable {R : Type*} [CommRing R]

structure Coaction (R : Type*) [CommRing R] where
  map : R →+* Polynomial R
  counit : (Polynomial.evalRingHom 1).comp map = RingHom.id R
  coassoc : (Polynomial.mapRingHom map).comp map = PolynomialDiagonal.diagonal.comp map

namespace Coaction
variable (c : Coaction R)

def piece (n : ℕ) : AddSubgroup R where
  carrier := {x | c.map x = Polynomial.monomial n x}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; simp_all only [Set.mem_ofPred_eq, map_add]
  neg_mem' := by intro x hx; simp_all only [Set.mem_ofPred_eq, map_neg]

theorem coefficient_mem (x : R) (n : ℕ) : (c.map x).coeff n ∈ c.piece n := by
  change c.map ((c.map x).coeff n) = Polynomial.monomial n ((c.map x).coeff n)
  have h := congrArg (fun p : Polynomial (Polynomial R) => p.coeff n)
    (RingHom.congr_fun c.coassoc x)
  simpa only [RingHom.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map, PolynomialDiagonal.diagonal_coeff] using h

theorem coefficient_of_mem {n : ℕ} {x : R} (hx : x ∈ c.piece n) (m : ℕ) :
    (c.map x).coeff m = if n = m then x else 0 := by
  change c.map x = Polynomial.monomial n x at hx
  rw [hx, Polynomial.coeff_monomial]

theorem sum_coefficients (x : R) : ∑ n ∈ (c.map x).support, (c.map x).coeff n = x := by
  have h := RingHom.congr_fun c.counit x
  simpa only [RingHom.comp_apply, RingHom.id_apply, Polynomial.coe_evalRingHom,
    Polynomial.eval_eq_sum, Polynomial.sum, one_pow, mul_one] using h

def decompose (x : R) : ⨁ n, c.piece n :=
  ∑ n ∈ (c.map x).support,
    DirectSum.of (fun n => c.piece n) n ⟨(c.map x).coeff n, c.coefficient_mem x n⟩

theorem decompose_apply (x : R) (n : ℕ) :
    ((c.decompose x n : c.piece n) : R) = (c.map x).coeff n := by
  classical
  by_cases hn : n ∈ (c.map x).support
  · simp [decompose, DirectSum.of_apply, hn]
  · have hz : (c.map x).coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    simp [decompose, DirectSum.of_apply, hn, hz]

def decomposeHom : R →+ ⨁ n, c.piece n where
  toFun := c.decompose
  map_zero' := by
    apply DirectSum.ext
    intro n
    apply Subtype.ext
    simp [c.decompose_apply]
  map_add' x y := by
    apply DirectSum.ext
    intro n
    apply Subtype.ext
    simp [c.decompose_apply]

theorem recompose_decompose (x : R) :
    DirectSum.coeAddMonoidHom c.piece (c.decompose x) = x := by
  simp only [decompose, map_sum, DirectSum.coeAddMonoidHom_of]
  exact c.sum_coefficients x

theorem decompose_of_mem (n : ℕ) (x : c.piece n) :
    c.decompose x = DirectSum.of (fun n => c.piece n) n x := by
  apply DirectSum.ext
  intro m
  apply Subtype.ext
  rw [c.decompose_apply, c.coefficient_of_mem x.property]
  by_cases h : n = m
  · subst m; simp
  · simp [DirectSum.of_apply, h]

@[instance_reducible] def decomposition : DirectSum.Decomposition c.piece :=
  DirectSum.Decomposition.ofAddHom c.piece c.decomposeHom
    (by ext x; exact c.recompose_decompose x)
    (by
      apply DirectSum.addHom_ext
      intro n x
      change c.decompose (DirectSum.coeAddMonoidHom c.piece (DirectSum.of _ n x)) = _
      rw [DirectSum.coeAddMonoidHom_of, c.decompose_of_mem]
      rfl)

@[instance_reducible] def grading : GradedRing c.piece where
  one_mem := by change c.map 1 = Polynomial.monomial 0 1; simp
  mul_mem := by
    intro m n x y hx hy
    change c.map x = Polynomial.monomial m x at hx
    change c.map y = Polynomial.monomial n y at hy
    change c.map (x * y) = Polynomial.monomial (m + n) (x * y)
    rw [map_mul, hx, hy, Polynomial.monomial_mul_monomial]
  toDecomposition := c.decomposition

end Coaction
end DiamondIntegral.Section4.PolynomialCoactionGrading
