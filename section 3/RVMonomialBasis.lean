import «section 3».RVMonomialMaps
import «section 3».MonomialResidueCoordinates
import «section 3».RVUnitValueHom
import Mathlib.Data.Set.Finite.Lattice
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}

def rvMonomialBasisBijection (S : Set M) (b : Module.Basis (Fin n) ℤ (Fin n → ℤ)) :
    DefinableBijection (rvZeroPattern (M := M) S (∅ : Set (Fin n))) (rvZeroPattern S (∅ : Set (Fin n))) :=
  rvMonomialTorusBijection S (integerBasisMatrix b) (integerBasisInverseMatrix b)
    (integerBasis_mul_inverse b) (integerBasisInverse_mul b)

theorem smith_basis_residue_tuple_values_finite {ι G Γ : Type} [Fintype ι] [DecidableEq ι]
    [CommGroup G] [CommGroup Γ] [HasUniqueRoots Γ]
    (v : G →* Γ) (A : Set (ι → G)) {N : Submodule ℤ (ι → ℤ)} {r : ℕ}
    (F : Module.Basis.SmithNormalForm N ι r)
    (hN : ∀ e ∈ N, (characterValueImage v A e).Finite) :
    ((fun x => fun i : Fin r => v (integerMonomialBasisEquiv F.bM x (F.f i))) '' A).Finite := by
  have hh := Set.Finite.pi' (smith_basis_coordinate_values_finite v A F hN)
  apply hh.subset
  rintro _ ⟨x,hx,rfl⟩ i
  exact ⟨x,hx,rfl⟩

/-- For actual RV units, all finite-value character constraints can be
placed in a single residue tuple by one original-ground monomial bijection. -/
theorem rv_exists_monomial_residue_coordinates
    (A : Set (Fin n → (CanonicalRV.RVSort M)ˣ)) (W : Set (Fin n → ℤ))
    (hW : ∀ e ∈ W, (characterValueImage (rvUnitValueHom (M := M)) A e).Finite) :
    ∃ r : ℕ, ∃ F : Module.Basis.SmithNormalForm (Submodule.span ℤ W) (Fin n) r,
      r ≤ n ∧
      ((fun x => fun i : Fin r => rvUnitValueHom (integerMonomialBasisEquiv F.bM x (F.f i))) '' A).Finite ∧
      (∀ e ∈ Submodule.span ℤ W, ∀ x y : Fin n → (CanonicalRV.RVSort M)ˣ,
        (∀ i, integerMonomialBasisEquiv F.bM x (F.f i) = integerMonomialBasisEquiv F.bM y (F.f i)) →
        integerCharacter e x = integerCharacter e y) := by
  obtain ⟨r,F,hr,hf,hdep⟩ := exists_monomial_residue_coordinates (rvUnitValueHom (M := M)) A W hW
  exact ⟨r,F,hr,smith_basis_residue_tuple_values_finite _ A F
    (characterValueImage_span_finite _ A W hW),hdep⟩
end DiamondIntegral.Section3
