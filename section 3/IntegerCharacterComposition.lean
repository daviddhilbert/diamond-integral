import «section 3».CharacterFiniteValues
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {ι : Type} [Fintype ι] {G : Type} [CommGroup G]

theorem integerCharacter_mul (e : ι → ℤ) (x y : ι → G) :
    integerCharacter e (x*y) = integerCharacter e x * integerCharacter e y := by
  simp only [integerCharacter,Pi.mul_apply,mul_zpow,Finset.prod_mul_distrib]

theorem integerCharacter_monomialMap {n m : ℕ} (e : Fin n → ℤ) (A : Matrix (Fin n) (Fin m) ℤ)
    (u : Fin m → G) :
    integerCharacter e (integerMonomialMap A u) = integerCharacter (fun j => ∑ i, e i * A i j) u :=
  congrFun (integerMonomialMap_comp (fun _ : Fin 1 => e) A u) 0
end DiamondIntegral.Section3
