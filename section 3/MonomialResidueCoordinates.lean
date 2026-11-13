import «section 3».CharacterFiniteValues
import Mathlib.LinearAlgebra.StdBasis
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace DiamondIntegral.Section3
variable {ι G Γ : Type} [Fintype ι] [DecidableEq ι] [CommGroup G] [CommGroup Γ]

theorem integerCharacter_depends_on_smith_coordinates {N : Submodule ℤ (ι → ℤ)} {r : ℕ}
    (F : Module.Basis.SmithNormalForm N ι r) (e : ι → ℤ) (he : e ∈ N)
    (x y : ι → G) (hxy : ∀ i, integerMonomialBasisEquiv F.bM x (F.f i) =
      integerMonomialBasisEquiv F.bM y (F.f i)) : integerCharacter e x = integerCharacter e y := by
  rw [← integerCharacter_basis_reconstruction F.bM e x,← integerCharacter_basis_reconstruction F.bM e y]
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hf : j ∈ Set.range F.f
  · obtain ⟨i,rfl⟩ := hf
    rw [hxy i]
  · have hz := F.repr_eq_zero_of_notMem_range (⟨e,he⟩ : N) hf
    simp only [hz,zpow_zero]

/-- Finite-value characters can simultaneously be placed in residue
coordinates by an integral monomial change. This is a local algebraic
normal-form step, with no definability premise added. -/
theorem exists_monomial_residue_coordinates [HasUniqueRoots Γ]
    (v : G →* Γ) {n : ℕ} (A : Set (Fin n → G)) (W : Set (Fin n → ℤ))
    (hW : ∀ e ∈ W, (characterValueImage v A e).Finite) :
    ∃ r : ℕ, ∃ F : Module.Basis.SmithNormalForm (Submodule.span ℤ W) (Fin n) r,
      r ≤ n ∧
      (∀ i : Fin r, ((fun x => v (integerMonomialBasisEquiv F.bM x (F.f i))) '' A).Finite) ∧
      (∀ e ∈ Submodule.span ℤ W, ∀ x y : Fin n → G,
        (∀ i, integerMonomialBasisEquiv F.bM x (F.f i) = integerMonomialBasisEquiv F.bM y (F.f i)) →
        integerCharacter e x = integerCharacter e y) := by
  obtain ⟨r,F⟩ := (Submodule.span ℤ W).smithNormalForm (Pi.basisFun ℤ (Fin n))
  refine ⟨r,F,?_,?_,?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_le_of_injective F.f F.f.injective
  · exact smith_basis_coordinate_values_finite v A F (characterValueImage_span_finite v A W hW)
  · exact integerCharacter_depends_on_smith_coordinates F
end DiamondIntegral.Section3
