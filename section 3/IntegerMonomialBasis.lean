import «section 3».IntegerMonomialMaps
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {ι G : Type} [Fintype ι] [DecidableEq ι] [CommGroup G]

def integerBasisMatrix (b : Module.Basis ι ℤ (ι → ℤ)) : Matrix ι ι ℤ := fun i j => b i j

def integerBasisInverseMatrix (b : Module.Basis ι ℤ (ι → ℤ)) : Matrix ι ι ℤ :=
  fun i j => b.repr (Pi.single i 1) j

theorem integerBasisInverse_mul (b : Module.Basis ι ℤ (ι → ℤ)) :
    integerBasisInverseMatrix b * integerBasisMatrix b = 1 := by
  ext i k
  have hh := congrFun (b.sum_repr (Pi.single i 1)) k
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at hh
  simpa only [integerBasisInverseMatrix,integerBasisMatrix,Matrix.mul_apply,Matrix.one_apply,
    Pi.single_apply,eq_comm] using hh

theorem integerBasis_mul_inverse (b : Module.Basis ι ℤ (ι → ℤ)) :
    integerBasisMatrix b * integerBasisInverseMatrix b = 1 :=
  mul_eq_one_comm.mp (integerBasisInverse_mul b)

def integerMonomialBasisEquiv (b : Module.Basis ι ℤ (ι → ℤ)) : (ι → G) ≃* (ι → G) :=
  integerMonomialEquiv (integerBasisMatrix b) (integerBasisInverseMatrix b)
    (integerBasis_mul_inverse b) (integerBasisInverse_mul b)
end DiamondIntegral.Section3
