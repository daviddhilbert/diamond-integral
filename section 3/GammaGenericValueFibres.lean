import «section 3».GammaGenericAngularCells
import «section 3».RVGroundAngularPartition
import «section 3».RVGammaFormValuePartition
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n : ℕ}

/-- A full Gamma-generic value fibre has no proper nonempty subset
definable over the original real/Gamma base. -/
theorem gammaGroundRVUnit_generic_value_fibre_invariant {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n)) (x : A)
    (hγ : GammaTupleIndependentOver B (rvUnitTupleValues x.val))
    (y : Fin n → (CanonicalRV.RVSort M)ˣ) (hxy : rvUnitTupleValues x.val = rvUnitTupleValues y) :
    y ∈ A.carrier := by
  have hA := (gammaGroundRVUnit_definable_iff A.carrier).mp A.definable
  obtain ⟨N,W,hW,hE,_,hcov⟩ := gammaGround_finite_angular_partition hκ hs h00 hc B hsmall
    (rvUnitValues '' A.carrier) hA
  obtain ⟨i,hi⟩ := (hcov x.val).mp ⟨x.val,x.property,rfl⟩
  let X := gammaGroundRVUnitSetOfBase (hc := hc) (W i) (hW i)
  have hy : y ∈ X.carrier := gammaGroundRVAngularCell_generic_fibre_invariant X (Classical.choice (hE i))
    ⟨x.val,hi⟩ hγ y hxy
  obtain ⟨z,hz,he⟩ := (hcov y).mpr ⟨i,hy⟩
  exact rvUnitValues_injective he ▸ hz

/-- An actual definable Gamma-valued map is constant on each full
Gamma-generic value fibre. The proof retains its original mixed ground. -/
theorem gammaGroundRVUnitGammaMap_generic_fibre_constant {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (A : GammaGroundDefSet hc B (rawRVUnitSpace (M := M) n))
    (ω : GammaGroundMap A (GammaGroundDefSet.univ hc B (volumeGammaSpace hc))) (x y : A)
    (hγ : GammaTupleIndependentOver B (rvUnitTupleValues x.val))
    (hxy : rvUnitTupleValues x.val = rvUnitTupleValues y.val) : ω x = ω y := by
  obtain ⟨J,Q,f,hQ,_,hcov,hf⟩ := gammaGroundRVUnitGammaForm_value_partition hκ hs h00 hsmall hγsmall A ω
  obtain ⟨j,hx⟩ := (hcov x.val).mp x.property
  have hy : y.val ∈ (Q j).carrier := gammaGroundRVUnit_generic_value_fibre_invariant hκ hs h00 hsmall
    (Q j) ⟨x.val,hx⟩ hγ y.val hxy
  apply Subtype.ext
  exact (hf j x hx).symm.trans ((congrArg (f j).val hxy).trans (hf j y hy))
end DiamondIntegral.Section3
