import «section 3».ResidueTupleGammaClosure
import «section 3».GammaGroundRVUnitCoordinates
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

def adjoinRVUnitTuple (B : Base (M := M)) (r : Fin n → (CanonicalRV.RVSort M)ˣ) : Base (M := M) :=
  ⟨B.real ∪ Set.range (rvUnitValues r),B.gamma⟩

/-- Adjoining any point of a finite-value-support RV set leaves the
Gamma definable closure unchanged. All final parameters remain original. -/
theorem gammaGroundRVUnit_residue_gamma_closure_iff {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (R : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (hR : (rvUnitTupleValues '' R.carrier).Finite) (r : R) (δ : Values.Gamma (M := M)) :
    GammaDefinableClosureAtBase (adjoinRVUnitTuple B r.val) δ ↔ GammaDefinableClosureAtBase B δ := by
  constructor
  · intro hd
    apply residue_tuple_gamma_algebraic_elimination hκ hs h00 B hsmall
      (rvUnitRawCoordinateImage R.carrier) (gammaGroundRVUnitCoordinate_definable R)
      (rvUnitRawCoordinateImage_finite_values R.carrier hR) (rvUnitValues r.val)
      (fun i => ⟨rvUnitValues r.val,⟨r.val,r.property,rfl⟩,rfl⟩) δ
    exact (gamma_algebraic_iff_definable_base (adjoinRVUnitTuple B r.val) δ).mpr hd
  · exact fun hd => hd.mono Set.subset_union_left Set.Subset.rfl
end DiamondIntegral.Section3
