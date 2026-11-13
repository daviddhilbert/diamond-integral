import «section 3».IntegerMonomialMaps
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
open scoped BigOperators
namespace DiamondIntegral.Section3
variable {Γ : Type} [CommGroup Γ] {n m : ℕ}

/-- Restricting an integral-affine formula to an identity slice leaves
the lower-left rectangular integer block and the corresponding shifts. -/
theorem integralAffine_identity_slice_bottom
    (C : Matrix (Fin (n+m)) (Fin (n+m)) ℤ) (δ : Fin (n+m) → Γ) (α : Fin n → Γ) :
    (fun j : Fin m => (δ * integerMonomialMap C (Fin.append α (fun _ : Fin m => (1 : Γ)))) (Fin.natAdd n j)) =
      (fun j => δ (Fin.natAdd n j)) *
        integerMonomialMap (fun j i => C (Fin.natAdd n j) (Fin.castAdd m i)) α := by
  funext j
  change δ (Fin.natAdd n j) *
      (∏ k : Fin (n+m), (Fin.append α (fun _ : Fin m => (1 : Γ)) k) ^ C (Fin.natAdd n j) k) = _
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left,Fin.append_right,one_zpow,Finset.prod_const_one,mul_one,
    Pi.mul_apply,integerMonomialMap]

end DiamondIntegral.Section3
