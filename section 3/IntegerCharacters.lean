import «section 3».IntegerMonomialBasis
import Mathlib.LinearAlgebra.FreeModule.PID
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {ι G : Type} [Fintype ι] [DecidableEq ι] [CommGroup G]

def integerCharacter (e : ι → ℤ) (x : ι → G) : G := ∏ j, x j ^ e j

theorem integerCharacter_smul (d : ℤ) (e : ι → ℤ) (x : ι → G) :
    integerCharacter (d • e) x = integerCharacter e x ^ d := by
  simp only [integerCharacter,Pi.smul_apply,smul_eq_mul]
  simp_rw [mul_comm d, zpow_mul]
  exact Finset.prod_zpow _ _ _

theorem integerCharacter_basis_reconstruction (b : Module.Basis ι ℤ (ι → ℤ))
    (e : ι → ℤ) (x : ι → G) :
    integerCharacter (fun i => b.repr e i) (integerMonomialBasisEquiv b x) = integerCharacter e x := by
  let C : Matrix (Fin 1) ι ℤ := fun _ i => b.repr e i
  have he : C * integerBasisMatrix b = fun _ : Fin 1 => e := by
    ext i j
    have hh := congrFun (b.sum_repr e) j
    simpa only [C,integerBasisMatrix,Matrix.mul_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hh
  have hh := congrFun (integerMonomialMap_comp C (integerBasisMatrix b) x) 0
  rw [he] at hh
  exact hh

/-- A Smith basis character is a nonzero integral power of one coordinate
of the unimodular monomial change. -/
theorem integerCharacter_smith {N : Submodule ℤ (ι → ℤ)} {r : ℕ}
    (F : Module.Basis.SmithNormalForm N ι r) (i : Fin r) (x : ι → G) :
    integerCharacter (F.bN i : ι → ℤ) x = (integerMonomialBasisEquiv F.bM x (F.f i)) ^ F.a i := by
  rw [F.snf,integerCharacter_smul]
  rfl

theorem smith_character_exponent_ne_zero {N : Submodule ℤ (ι → ℤ)} {r : ℕ}
    (F : Module.Basis.SmithNormalForm N ι r) (i : Fin r) : F.a i ≠ 0 := by
  intro ha
  have hn : (F.bN i : ι → ℤ) ≠ 0 := fun h => F.bN.ne_zero i (Subtype.ext h)
  apply hn
  rw [F.snf,ha,zero_smul]
end DiamondIntegral.Section3
