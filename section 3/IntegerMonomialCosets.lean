import «section 3».SmithCharacterFibres
import «section 3».RVUnitValueHom
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {ι G H Γ : Type} [Fintype ι] [DecidableEq ι]
variable [CommGroup G] [CommGroup H] [CommGroup Γ]

theorem integerMonomialMap_mul (A : Matrix ι ι ℤ) (x y : ι → G) :
    integerMonomialMap A (x*y) = integerMonomialMap A x * integerMonomialMap A y := by
  funext i
  simp only [integerMonomialMap,Pi.mul_apply,mul_zpow,Finset.prod_mul_distrib]

/-- Testing a monomial map on one value coset detects its action on
every embedded residue torus. No section of the value map is chosen. -/
theorem integerMonomialMap_residue_injective_of_coset_injective
    (v : G →* Γ) (ρ : H →* G) (hρ : Function.Injective ρ)
    (hvalue : ∀ h, v (ρ h) = 1) (A : Matrix ι ι ℤ) (x : ι → G)
    (hinj : Set.InjOn (integerMonomialMap A) {y | (fun i => v (y i)) = fun i => v (x i)}) :
    Function.Injective (integerMonomialMap (G := H) A) := by
  intro a b hab
  let u : ι → G := x * (ρ ∘ a)
  let w : ι → G := x * (ρ ∘ b)
  have hu : u ∈ {y | (fun i => v (y i)) = fun i => v (x i)} := by
    funext i
    exact (map_mul v _ _).trans (by simp only [Function.comp_apply,hvalue,mul_one])
  have hw : w ∈ {y | (fun i => v (y i)) = fun i => v (x i)} := by
    funext i
    exact (map_mul v _ _).trans (by simp only [Function.comp_apply,hvalue,mul_one])
  have he : integerMonomialMap A u = integerMonomialMap A w := by
    rw [integerMonomialMap_mul,integerMonomialMap_mul]
    congr 1
    exact (monomial_map_value ρ A a).symm.trans
      ((congrArg (fun z => ρ ∘ z) hab).trans (monomial_map_value ρ A b))
  have huw := hinj hu hw he
  funext i
  apply hρ
  apply mul_left_cancel (a := x i)
  exact congrFun huw i

theorem integerMonomialMap_coset_det_isUnit [Nontrivial H]
    (hpower : ∀ d : ℤ, Function.Injective (fun h : H => h ^ d) → IsUnit d)
    (v : G →* Γ) (ρ : H →* G) (hρ : Function.Injective ρ) (hvalue : ∀ h, v (ρ h) = 1)
    (A : Matrix ι ι ℤ) (x : ι → G)
    (hinj : Set.InjOn (integerMonomialMap A) {y | (fun i => v (y i)) = fun i => v (x i)}) :
    IsUnit A.det :=
  integerMonomialMap_det_isUnit_of_injective hpower A
    (integerMonomialMap_residue_injective_of_coset_injective v ρ hρ hvalue A x hinj)
end DiamondIntegral.Section3
