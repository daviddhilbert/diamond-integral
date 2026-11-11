import «section 2».ClosedBoundedImageBounded
import «section 2».SmallVFGeneratedBase

/-! Lemma 2.48 over an arbitrary real parameter base. A small temporary
VF-generated base is constructed from the finite defining parameters;
VF-generation is not an assumption on the original ground base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem lemma_2_48
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A)) (hAcl : IsClosed A)
    (hAb : ∃ γ : Gamma M, ∀ x ∈ A, ∀ i, γ.val ≤ vfValue (x i))
    (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x}))) (hfcont : ContinuousOn f A) :
    IsClosed (f '' A) ∧ ∃ γ : Gamma M, ∀ y ∈ f '' A, ∀ i, γ.val ≤ vfValue (y i) := by
  obtain ⟨C,hsmall,hAC,hfC,B,x,hx0,hxv⟩ := exists_small_vf_generated_base_for_two_definable hv hκ
    (vfValues '' A) hA (vfCorrespondenceGraph A (fun x => {f x})) hf
  have hnt : ∃ x : B.field, x ≠ 0 ∧ Valued.v x.val ≠ 1 := ⟨x,hx0,ne_of_lt hxv⟩
  exact ⟨lemma_2_48_image_closed_vf_generated h00 hc hκ.le hs hv C.toSubstructure B hnt hsmall
      A hAC hAcl hAb f hfC hfcont,
    lemma_2_48_image_bounded_vf_generated h00 hc hκ.le hs hv C.toSubstructure B hnt hsmall
      A hAC hAcl hAb f hfC hfcont⟩

end DiamondIntegral.Section2
