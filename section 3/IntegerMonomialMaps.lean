import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {ι κ τ G : Type} [Fintype ι] [Fintype κ] [Fintype τ] [CommGroup G]

theorem integer_power_sum (g : G) (s : Finset κ) (e : κ → ℤ) :
    g ^ (∑ j ∈ s, e j) = ∏ j ∈ s, g ^ e j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha,Finset.prod_insert ha,zpow_add,ih]

def integerMonomialMap (A : Matrix ι κ ℤ) (x : κ → G) : ι → G := fun i => ∏ j, x j ^ A i j

theorem integerMonomialMap_comp (A : Matrix ι κ ℤ) (B : Matrix κ τ ℤ) (x : τ → G) :
    integerMonomialMap A (integerMonomialMap B x) = integerMonomialMap (A * B) x := by
  funext i
  simp only [integerMonomialMap,Matrix.mul_apply]
  simp_rw [← Finset.prod_zpow]
  simp_rw [← zpow_mul]
  simp_rw [integer_power_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.prod_congr rfl
  intro k hk
  rw [Int.mul_comm]

theorem integerMonomialMap_one [DecidableEq ι] (x : ι → G) : integerMonomialMap (1 : Matrix ι ι ℤ) x = x := by
  funext i
  simp [integerMonomialMap,Matrix.one_apply]

/-- An integral matrix with a two-sided integral inverse gives a genuine
monomial group isomorphism on the whole torus. -/
def integerMonomialEquiv [DecidableEq ι] (A B : Matrix ι ι ℤ)
    (hAB : A * B = 1) (hBA : B * A = 1) : (ι → G) ≃* (ι → G) where
  toFun := integerMonomialMap A
  invFun := integerMonomialMap B
  left_inv x := by rw [integerMonomialMap_comp,hBA,integerMonomialMap_one]
  right_inv x := by rw [integerMonomialMap_comp,hAB,integerMonomialMap_one]
  map_mul' x y := by
    funext i
    simp only [integerMonomialMap,Pi.mul_apply,mul_zpow,Finset.prod_mul_distrib]
end DiamondIntegral.Section3
