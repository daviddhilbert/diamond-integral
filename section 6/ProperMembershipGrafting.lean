import «section 6».ProperMembershipLabels
import «section 6».BoundedUnaryHomeChains

/-! Actual proper membership grafting is a relatively unary identity
on VF coordinates. Any subsequent label-retaining preparation with an
RV-pullback target automatically prepares every protected subset. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {A C : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

theorem restricted_image_eq_retained_tag
    (f : Map A B) (hf : Function.Bijective f) (hCA : C.carrier ⊆ A.carrier) (j : Fin s)
    (hMem : ∀ p : A,p.val ∈ C.carrier ↔ (f p).val.2 j=branchTag (M := M) true) :
    (f.restrict hCA).image.carrier={q | q ∈ B.carrier ∧ q.2 j=branchTag (M := M) true} := by
  ext q
  constructor
  · rintro ⟨p,hp⟩
    let a : A := ⟨p.val,hCA p.property⟩
    exact ⟨hp ▸ (f a).property,hp ▸ ((hMem a).mp p.property)⟩
  · rintro ⟨hq,hTag⟩
    obtain ⟨p,hp⟩ := hf.surjective ⟨q,hq⟩
    have hC : p.val ∈ C.carrier := (hMem p).mpr ((congrArg (fun w : B => w.val.2 j) hp).trans hTag)
    exact ⟨⟨p.val,hC⟩,congrArg Subtype.val hp⟩

theorem restricted_image_rvPullback_of_retained_tag
    (f : Map A B) (hf : Function.Bijective f) (hCA : C.carrier ⊆ A.carrier) (j : Fin s)
    (hMem : ∀ p : A,p.val ∈ C.carrier ↔ (f p).val.2 j=branchTag (M := M) true)
    (hB : IsRVPullback B.carrier) : IsRVPullback (f.restrict hCA).image.carrier := by
  rw [restricted_image_eq_retained_tag f hf hCA j hMem]
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨z,hz,hVF,hRV⟩ := (mem_rvHull_iff _ q).mp hq
  exact ⟨rvPullback_mem_of_sameRV hB hz.1 hVF hRV,(congrFun hRV j).symm.trans hz.2⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem properMembershipGraft_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hn : 0<n) (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S) (hC : ∀ i,ProperInvariant S (C i).carrier) :
    ∃ F : RetainedUnaryHomeChain (G := G) S (graft hc (properMembershipLabels A C)) (Fin.castAdd k),
      VFDoublyBounded A.carrier → F.DoublyBounded := by
  let τ := properMembershipLabels A C
  have hτ := properMembershipLabels_properCovariant h00 hc hκ hs hv A hA C hC
  let F : RetainedUnaryHomeChain (G := G) S (graft hc τ) (Fin.castAdd k) :=
    .unary ⟨0,hn⟩ (graft_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ τ hA hτ)
      (fun _ _ _ => rfl) (fun p _ => graft_unit_derivative hc hv τ hτ p)
      (fun p i => by simp only [graft_apply,Fin.append_left])
  refine ⟨F,fun hD => ⟨hD,?_⟩⟩
  obtain ⟨α,hα⟩ := hD
  exact ⟨α,by rintro q ⟨p,rfl⟩ i; exact hα p.val p.property i⟩

theorem properMembershipGraft_mem_iff
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S) (p : A) (i : Fin k) :
    p.val ∈ (C i).carrier ↔ (graft hc (properMembershipLabels A C) p).val.2 (Fin.natAdd r i)=branchTag (M := M) true := by
  simp only [graft_apply,Fin.append_right,properMembershipLabels_value]
  constructor
  · intro hp
    simp only [hp,decide_true]
  · intro he
    exact of_decide_eq_true (branchTag_injective h00 he)

theorem properMembershipGraft_prepares_protected_images
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S) (hCA : ∀ i,(C i).carrier ⊆ A.carrier)
    (f : Map (graftMap hc (properMembershipLabels A C)).image B) (hf : Function.Bijective f)
    (π : Fin (r+k) → Fin s)
    (hRetain : ∀ p,∀ i,(f p).val.2 (π i)=p.val.2 i) (hB : IsRVPullback B.carrier) (i : Fin k) :
    IsRVPullback (((f.comp (graft hc (properMembershipLabels A C))).restrict (hCA i)).image.carrier) := by
  apply restricted_image_rvPullback_of_retained_tag (f.comp (graft hc (properMembershipLabels A C)))
    (hf.comp (graft_bijective hc _)) (hCA i) (π (Fin.natAdd r i)) ?_ hB
  intro p
  change p.val ∈ (C i).carrier ↔ (f (graft hc (properMembershipLabels A C) p)).val.2 (π (Fin.natAdd r i))=branchTag (M := M) true
  rw [hRetain]
  exact properMembershipGraft_mem_iff h00 hc A C p i

end DiamondIntegral.Section6
