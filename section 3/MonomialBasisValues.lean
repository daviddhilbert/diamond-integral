import «section 3».RVMonomialBasis
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3

theorem integerMonomialBasis_value_eq_of_coordinates {ι G Γ : Type}
    [Fintype ι] [DecidableEq ι] [CommGroup G] [CommGroup Γ]
    (v : G →* Γ) (b : Module.Basis ι ℤ (ι → ℤ)) (x y : ι → G)
    (h : ∀ i, v (integerMonomialBasisEquiv b x i) = v (integerMonomialBasisEquiv b y i)) :
    ∀ i, v (x i) = v (y i) := by
  have he : (fun i => v (x i)) = (fun i => v (y i)) := by
    apply (integerMonomialBasisEquiv (G := Γ) b).injective
    change integerMonomialMap (integerBasisMatrix b) (fun i => v (x i)) =
      integerMonomialMap (integerBasisMatrix b) (fun i => v (y i))
    rw [← monomial_map_value v (integerBasisMatrix b) x,← monomial_map_value v (integerBasisMatrix b) y]
    exact funext h
  exact fun i => congrFun he i

theorem integerMonomialBasis_value_eq_of_active_and_free {ι G Γ : Type}
    [Fintype ι] [DecidableEq ι] [CommGroup G] [CommGroup Γ]
    (v : G →* Γ) {N : Submodule ℤ (ι → ℤ)} {r : ℕ}
    (F : Module.Basis.SmithNormalForm N ι r) (x y : ι → G)
    (hactive : ∀ i, integerMonomialBasisEquiv F.bM x (F.f i) = integerMonomialBasisEquiv F.bM y (F.f i))
    (hfree : ∀ j, j ∉ Set.range F.f → v (integerMonomialBasisEquiv F.bM x j) = v (integerMonomialBasisEquiv F.bM y j)) :
    ∀ i, v (x i) = v (y i) := by
  apply integerMonomialBasis_value_eq_of_coordinates v F.bM x y
  intro j
  by_cases hj : j ∈ Set.range F.f
  · obtain ⟨i,rfl⟩ := hj
    exact congrArg v (hactive i)
  · exact hfree j hj
end DiamondIntegral.Section3
