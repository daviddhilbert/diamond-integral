import «section 3».IntegerMonomialMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {ι κ τ G : Type} [Fintype ι] [Fintype κ] [Fintype τ] [CommGroup G]

theorem integerMonomialMap_mul_rect (A : Matrix ι κ ℤ) (x y : κ → G) :
    integerMonomialMap A (x*y) = integerMonomialMap A x * integerMonomialMap A y := by
  funext i
  simp only [integerMonomialMap,Pi.mul_apply,mul_zpow,Finset.prod_mul_distrib]

theorem integerMonomialMap_inv_rect (A : Matrix ι κ ℤ) (x : κ → G) :
    integerMonomialMap A x⁻¹ = (integerMonomialMap A x)⁻¹ := by
  funext i
  simp only [integerMonomialMap,Pi.inv_apply,inv_zpow,Finset.prod_inv_distrib]

theorem integerMonomialMap_sub (A B : Matrix ι κ ℤ) (x : κ → G) :
    integerMonomialMap (A-B) x = integerMonomialMap A x * (integerMonomialMap B x)⁻¹ := by
  funext i
  simp only [integerMonomialMap,Matrix.sub_apply,zpow_sub,Finset.prod_mul_distrib,Finset.prod_inv_distrib,Pi.mul_apply,Pi.inv_apply]

variable [DecidableEq κ]

/-- Elimination of a square unimodular free block preserves integral
exponents and makes every new coefficient an integral residue monomial. -/
theorem integerMonomialMap_eliminate_coefficients
    (A : Matrix κ κ ℤ) (hA : IsUnit A.det) (B : Matrix ι κ ℤ)
    (C : Matrix κ τ ℤ) (D : Matrix ι τ ℤ) (r : τ → G) (u : κ → G) :
    integerMonomialMap D r * integerMonomialMap B u =
      integerMonomialMap (D-(B*A⁻¹)*C) r * integerMonomialMap (B*A⁻¹)
        (integerMonomialMap C r * integerMonomialMap A u) := by
  have hBA : (B*A⁻¹)*A = B := by rw [Matrix.mul_assoc,Matrix.nonsing_inv_mul A hA,Matrix.mul_one]
  rw [integerMonomialMap_sub,integerMonomialMap_mul_rect,← integerMonomialMap_comp (B*A⁻¹) C r,
    integerMonomialMap_comp (B*A⁻¹) A u,hBA]
  simp only [mul_assoc,inv_mul_cancel_left]
end DiamondIntegral.Section3
