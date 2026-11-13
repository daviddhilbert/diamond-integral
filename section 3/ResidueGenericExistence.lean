import «section 3».RVValueFibreIndependence
import Section4.SmallGeneratedBase
import Section4.ResidueTupleRank
import Section4.EarlierRVInputs
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

/-- Genuine saturation supplies residue-field independent tuples over
any countable coefficient subfield inside the same ambient model. -/
theorem exists_residue_generic_over_countable {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (E : Subfield (ModelResidue M)) (hE : Cardinal.mk E ≤ Cardinal.aleph0) (n : ℕ) :
    ∃ x : Fin n → ModelResidue M, AlgebraicIndependent E x := by
  let S : Set M := Set.range (fun e : E => (residueRV (e : ModelResidue M)).val)
  have hS : Cardinal.mk S < κ := Cardinal.mk_range_le.trans_lt (hE.trans_lt hκ)
  let B := Substructure.closure LRV S
  have hB : Cardinal.mk B < κ := small_generated_substructure hκ S hS
  obtain ⟨t,ht,hval⟩ := exists_independent_gamma_fibre_tuple hκ.le hs h00
    (B : Set M) hB (fun _ : Fin n => (1 : Values.Gamma (M := M)))
  have hres (i : Fin n) : ∃ a : ModelResidue M, residueRV a = t i := by
    apply exists_residueRV
    apply (RVOperations.inK_iff (t i)).mpr
    right
    change Values.valueEquiv Values.presentationValuation Values.presentation_compatible
      (Values.vrv (t i)) = 1
    rw [hval i,Values.gamma_val_one]
    exact Values.paperValue_one
  choose x hx using hres
  have he : residueRV ∘ x = t := funext hx
  have hi : AlgebraicIndependent (residueParameterField B) x := by
    apply (residue_independent_iff_rvTupleRank_eq_arity hc
      (rvExchangeInput_of_earlier hκ.le hs h00) B x).mpr
    rw [he]
    exact rvTupleRank_eq_arity_of_sequence hc (rvExchangeInput_of_earlier hκ.le hs h00) _ _ ht
  have hEB : E ≤ residueParameterField B := by
    intro e he
    change (residueRV e).val ∈ B
    exact Substructure.subset_closure ⟨⟨e,he⟩,rfl⟩
  let i := Subfield.inclusion hEB
  letI : Algebra E (residueParameterField B) := i.toAlgebra
  letI : IsScalarTower E (residueParameterField B) (ModelResidue M) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ⟨x,hi.restrictScalars i.injective⟩

end DiamondIntegral.Section3
