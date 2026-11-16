import «section 6».HeadBranchedShearFusion
import «section 6».FibrePreparationBases

/-! Branch-data existence in every positive VF dimension, by a uniform
induction in the actual VF-generated parameter base. Only the actual VF
head is adjoined on each fibre. Every bounded source consequently has
an actual strengthened first contraction stage. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem branched_shear_data_all_dimensions
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (n : ℕ) :
    ∀ (S V : Set M),Cardinal.mk S < κ →
      NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M) →
      (∀ a ∈ V,iVF a) → V ⊆ S → S ⊆ algebraicClosureSet V →
      (∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1) →
      ∀ r,∀ A : DefSet (rawMixedSpace (M := M) (n+1) r) S,ProperInvariant S A.carrier →
        Nonempty (BranchedShearData (G := G) A) := by
  induction n with
  | zero =>
    intro S V hsmall hΓ hV hVS hSV hnt r A hA
    exact exists_unary_branched_shear_data h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA
  | succ n ih =>
    intro S V hsmall hΓ hV hVS hSV hnt r A hA
    apply branched_shear_data_of_head_witnesses h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA
    intro a
    let z : Fin 1 → M := fun _ => a.val
    obtain ⟨hV',hVS',hSV',hnt',hsmall',hΓ'⟩ := vf_preparation_support_adjoin_tuple
      hV hVS hSV hnt hκ.le hsmall hΓ z (fun _ => a.property)
    exact ih (S ∪ Set.range z) (V ∪ Set.range z) hsmall' hΓ' hV' hVS' hSV' hnt' r
      ((headFibreTemplate A).fibre z) (headFibreTemplate_properInvariant A hA a)

theorem exists_shear_contraction_stage_all_dimensions
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S V : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    {n r : ℕ} (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) :
    Nonempty (ShearContractionStage (G := G) A) := by
  obtain ⟨D⟩ := branched_shear_data_all_dimensions h00 hc linear hκ hs hv n S V hsmall hΓ hV hVS hSV hnt r A hA
  exact ⟨D.toStage h00 hc linear hκ hs hv hsmall hΓ hA hAD⟩

end DiamondIntegral.Section6
