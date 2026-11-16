import «section 6».AmbientBoundaryCoreImages

/-! Actual bijective preparations carry a source complement onto the
target complement of its literal core image. RV-pullback geometry then
passes to that entire complement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

theorem rvPullback_sdiff {A B : Set (Mixed M n r)} (hA : IsRVPullback A) (hB : IsRVPullback B) :
    IsRVPullback (A \ B) := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨p,hp,hVF,hLabels⟩ := (mem_rvHull_iff (A \ B) q).mp hq
  exact ⟨rvPullback_mem_of_sameRV hA hp.1 hVF hLabels,
    fun hqB => hp.2 (rvPullback_mem_of_sameRV hB hqB hVF.symm hLabels.symm)⟩

def properSubsetComplement
    (A C : DefSet (rawMixedSpace (M := M) n r) S) : DefSet (rawMixedSpace (M := M) n r) S :=
  ⟨A.carrier \ C.carrier,A.definable.sdiff _ C.definable⟩

theorem image_complement_eq
    {A C : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Bijective f) (hCA : C.carrier ⊆ A.carrier) :
    (f.restrict (show (properSubsetComplement A C).carrier ⊆ A.carrier from fun _ hp => hp.1)).image.carrier=
      B.carrier \ (f.restrict hCA).image.carrier := by
  ext q
  constructor
  · rintro ⟨p,hp⟩
    let a : A := ⟨p.val,p.property.1⟩
    change (f a).val=q at hp
    refine ⟨hp ▸ (f a).property,?_⟩
    rintro ⟨c,hc⟩
    let b : A := ⟨c.val,hCA c.property⟩
    have he : b=a := hf.injective (Subtype.ext (hc.trans hp.symm))
    exact p.property.2 ((congrArg Subtype.val he) ▸ c.property)
  · rintro ⟨hq,hOut⟩
    obtain ⟨p,hp⟩ := hf.surjective ⟨q,hq⟩
    have hNot : p.val ∉ C.carrier := by
      intro hC
      exact hOut ⟨⟨p.val,hC⟩,congrArg Subtype.val hp⟩
    exact ⟨⟨p.val,p.property,hNot⟩,congrArg Subtype.val hp⟩

theorem image_complement_rvPullback
    {A C : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Bijective f) (hCA : C.carrier ⊆ A.carrier)
    (hB : IsRVPullback B.carrier) (hCore : IsRVPullback (f.restrict hCA).image.carrier) :
    IsRVPullback (f.restrict (show (properSubsetComplement A C).carrier ⊆ A.carrier from fun _ hp => hp.1)).image.carrier := by
  rw [image_complement_eq f hf hCA]
  exact rvPullback_sdiff hB hCore

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem regularized_centripetal_restriction_image
    (E : CentripetalData (G := G) A) (C : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : C.carrier ⊆ A.carrier) :
    ((centripetalStepMap E).restrict hCA).image.carrier=
      regularize '' (E.bijection.restrict hCA).image.carrier := by
  ext q
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨(E.bijection ⟨p.val,hCA p.property⟩).val,⟨p,rfl⟩,hp⟩
  · rintro ⟨x,⟨p,hp⟩,hx⟩
    exact ⟨p,(congrArg regularize hp).trans hx⟩

theorem regularized_centripetal_restriction_rvPullback
    (E : CentripetalData (G := G) A) (C : DefSet (rawMixedSpace (M := M) 1 r) S)
    (hCA : C.carrier ⊆ A.carrier) (hCore : IsRVPullback (E.bijection.restrict hCA).image.carrier) :
    IsRVPullback ((centripetalStepMap E).restrict hCA).image.carrier := by
  rw [regularized_centripetal_restriction_image E C hCA]
  have h := regularization_rvPullback (E.bijection.restrict hCA).image hCore
  rwa [regularization_carrier] at h

end DiamondIntegral.Section6
