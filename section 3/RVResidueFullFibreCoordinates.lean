import «section 3».RVResidueNormalizedPoints
import «section 3».RVUnitGammaMaps
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- The kernel of the actual RV value map consists exactly of the
nonzero residue-field points. -/
theorem exists_residueUnitToRV_of_value_one (u : (CanonicalRV.RVSort M)ˣ)
    (hu : rvUnitValueHom u = 1) : ∃ z : (ModelResidue M)ˣ, residueUnitToRV z = u := by
  have hv : Values.vrv (u : CanonicalRV.RVSort M) = 1 :=
    (congrArg Subtype.val hu).trans Values.gamma_val_one
  have hk : ValuedModelMap.inK (u : CanonicalRV.RVSort M) := by
    apply (RVOperations.inK_iff _).mpr
    right
    change Values.valueEquiv Values.presentationValuation Values.presentation_compatible
      (Values.vrv (u : CanonicalRV.RVSort M)) = 1
    rw [hv]
    exact Values.paperValue_one
  obtain ⟨z,hz⟩ := exists_residueRV hk
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    exact Units.ne_zero u (hz.symm.trans residueRV_zero)
  refine ⟨Units.mk0 z hz0,?_⟩
  apply Units.ext
  exact hz

/-- Any point of the full value fibre has unique residue coordinates
after a proof-only normalization; no coordinate is added to the ground. -/
theorem rvNormalizedPoint_surjective_on_fibre
    (a b : (CanonicalRV.RVSort M)ˣ) (h : rvUnitValueHom b = rvUnitValueHom a) :
    ∃ z : ModelResidue M, z ≠ 0 ∧ rvNormalizedPoint a z = (b : CanonicalRV.RVSort M) := by
  have hv : rvUnitValueHom (a⁻¹*b) = 1 := by rw [map_mul,map_inv,h,inv_mul_cancel]
  obtain ⟨z,hz⟩ := exists_residueUnitToRV_of_value_one (a⁻¹*b) hv
  refine ⟨z.val,Units.ne_zero z,?_⟩
  have he : a * residueUnitToRV z = b := by rw [hz,mul_inv_cancel_left]
  exact congrArg Units.val he

theorem rvNormalizedTuple_surjective_on_fibre {n : ℕ}
    (a b : Fin n → (CanonicalRV.RVSort M)ˣ) (h : rvUnitTupleValues b = rvUnitTupleValues a) :
    ∃ z : Fin n → ModelResidue M, (∀ i, z i ≠ 0) ∧
      rvNormalizedTuple a z = rvUnitValues b := by
  choose z hz0 hz using fun i => rvNormalizedPoint_surjective_on_fibre (a i) (b i) (congrFun h i)
  exact ⟨z,hz0,funext (fun i => congrArg Subtype.val (hz i))⟩

end DiamondIntegral.Section3
