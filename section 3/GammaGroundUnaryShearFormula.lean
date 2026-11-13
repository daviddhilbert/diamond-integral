import «section 3».IntegerMonomialMaps
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {Γ : Type} [CommGroup Γ]

/-- Restricting a two-dimensional integral-affine formula to its
identity slice leaves an arbitrary integer slope in the first variable. -/
theorem integralAffine_shear_slice_coordinate
    (C : Matrix (Fin 2) (Fin 2) ℤ) (δ : Fin 2 → Γ) (α : Fin 1 → Γ) :
    (δ * integerMonomialMap C (Fin.append α (fun _ : Fin 1 => (1 : Γ)))) (1 : Fin 2) =
      δ 1 * α 0 ^ C 1 0 := by
  change δ 1 * (∏ j : Fin 2, (Fin.append α (fun _ : Fin 1 => (1 : Γ)) j) ^ C 1 j) = _
  rw [Fin.prod_univ_two]
  simp [Fin.append,Fin.addCases]

end DiamondIntegral.Section3
