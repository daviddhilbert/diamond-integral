import «section 2».BoundaryDimension
import Section4.RealPresentations

/-! The raw theorem is exactly the RV-boundary statement for actual
VF tuples, with the manuscript's complement taken inside VF^n. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n : ℕ}

theorem rawVFComplement_vfValues (A : Set (Fin n → VF M)) :
    rawVFComplement (vfValues '' A) = vfValues '' Aᶜ := by
  ext x
  constructor
  · rintro ⟨hx,hxA⟩
    let a : Fin n → VF M := fun j => ⟨x j,hx j⟩
    exact ⟨a,fun ha => hxA ⟨a,ha,rfl⟩,rfl⟩
  · rintro ⟨a,ha,rfl⟩
    refine ⟨fun j => (a j).property,?_⟩
    rintro ⟨b,hb,he⟩
    exact ha (vfValues_injective he ▸ hb)

theorem rawRVImage_vfValues (A : Set (Fin n → VF M)) :
    rawRVImage (vfValues '' A) = tupleRV M '' A := by
  ext t
  constructor
  · rintro ⟨x,hxt,a,ha,hax⟩
    subst x
    exact ⟨a,ha,funext (fun j => Subtype.ext (hxt j).2)⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨vfValues a,(fun j => ⟨(a j).property,rfl⟩),a,ha,rfl⟩

theorem rawRVBoundary_vfValues (A : Set (Fin n → VF M)) :
    rawRVBoundary (vfValues '' A) = tupleRV M '' A ∩ tupleRV M '' Aᶜ := by
  rw [rawRVBoundary_eq_inter,rawVFComplement_vfValues,
    rawRVImage_vfValues,rawRVImage_vfValues]

theorem lemma_2_35_vf
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ) (S : Set M) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (unary : ∀ E : ParameterBase M, UnaryDiscAtomicityInput E)
    (rvbase : ∀ E : ParameterBase M, UnaryOpenDiscRVBaseChangeInput E)
    (image : ∀ E : ParameterBase M, OpenDiscNamesImageInput E)
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A)) :
    rvDimension S (tupleRV M '' A ∩ tupleRV M '' Aᶜ) < (n : WithBot ℕ) := by
  have hAv : DefinableOver S (fun _ => .vf) (vfValues '' A) :=
    SpecialTransformations.Section3.raw_definableOver_sorted hc S _ _ hA
      (by rintro x ⟨a,ha,rfl⟩ j; exact (a j).property)
  rw [← rawRVBoundary_vfValues]
  exact lemma_2_35 hc h00 hs S hsmall hΓ unary rvbase image _ hAv

end DiamondIntegral.Section2
