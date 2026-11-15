import «section 5».VFFieldSubstructure
import «section 3».TermGammaValue
import Mathlib.SetTheory.Cardinal.Subfield

/-! Exact smallness and real-parameter elimination for the genuine
VF-generated field presentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open CanonicalRV ValuedModelMap DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M))

theorem vfFieldSubstructure_small (F : Subfield (VFType (M := M)))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hF : Cardinal.mk F < κ) :
    Cardinal.mk (vfFieldSubstructure hc F) < κ := by
  change Cardinal.mk ((vfFieldNames F ∪ Subtype.val '' vfFieldRVImage F) : Set M) < κ
  have h₁ : Cardinal.mk (vfFieldNames F) ≤ Cardinal.mk F := Cardinal.mk_image_le
  have h₂ : Cardinal.mk (Subtype.val '' vfFieldRVImage F) ≤ Cardinal.mk F :=
    Cardinal.mk_image_le.trans Cardinal.mk_image_le
  exact (Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hκ (h₁.trans_lt hF) (h₂.trans_lt hF))

theorem vfParameterField_small (S : Set M) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hS : Cardinal.mk S < κ) : Cardinal.mk (vfParameterField S) < κ := by
  apply (Subfield.cardinalMk_closure_le_max {x : VFType (M := M) | x.val ∈ S}).trans_lt
  apply max_lt
  · let f : {x : VFType (M := M) | x.val ∈ S} → S := fun x => ⟨x.val.val,x.property⟩
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : S => z.val) h
    exact (Cardinal.mk_le_of_injective hf).trans_lt hS
  · exact hκ

theorem vfParameterFieldSubstructure_names (S : Set M) (x : M)
    (hx : x ∈ (vfFieldSubstructure hc (vfParameterField S) : Set M)) :
    ∃ σ, DefinableClosureAt S σ x := by
  rcases hx with ⟨a,ha,rfl⟩ | ⟨r,⟨a,ha,har⟩,rfl⟩
  · exact ⟨.vf,vfParameterField_le_definableClosureField S ha⟩
  · have hd : DefinableClosureAt S .rv (encodedRv a).val :=
      definableClosureAt_function_symbol S Fn.rvMap ![a.val]
        (by intro i; fin_cases i; exact a.property)
        (by intro i; fin_cases i; exact vfParameterField_le_definableClosureField S ha)
    exact ⟨.rv,congrArg Subtype.val har ▸ hd⟩

end DiamondIntegral.Section5
