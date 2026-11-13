import «section 3».GammaGenericAngularCells
import «section 3».ResidueGammaClosureInvariant
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n m : ℕ}

/-- Gamma independence survives naming an arbitrary point of a
finite-value-support RV set. -/
theorem gammaGroundRVUnit_residue_gamma_independent_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite) (r : R) (γ : Fin m → Values.Gamma (M := M)) :
    GammaTupleIndependentOver (adjoinRVUnitTuple B r.val) γ ↔ GammaTupleIndependentOver B γ := by
  have he := fun e : Fin m → ℤ => gammaGroundRVUnit_residue_gamma_closure_iff hκ hs h00 hsmall R hR r
    (integerCharacter e γ)
  exact ⟨fun h e he' => h e ((he e).mpr he'),fun h e he' => h e ((he e).mp he')⟩
end DiamondIntegral.Section3
