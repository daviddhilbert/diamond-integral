import «section 6».RVRefinementPieces
import «section 6».DoublyBoundedPullbackInvariance

/-! The actual portion of an old ambient covered by a label refinement.
All full fibres and bounds are retained, with no coverage assumption. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.RVRefinementFrame
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def oldMap (X : RVRefinementFrame A) : Map X.base A :=
  (selectRVLabelsMap X.base X.labels).corestrict (fun p => X.source_subset p.val p.property)

def coveredBase (X : RVRefinementFrame A) := X.oldMap.image

theorem coveredBase_subset (X : RVRefinementFrame A) : X.coveredBase.carrier ⊆ A.carrier := by
  rintro q ⟨p,hp⟩
  exact hp ▸ (X.oldMap p).property

theorem source_subset_covered (X : RVRefinementFrame A) (p : X.base) :
    (p.val.1,p.val.2 ∘ X.labels) ∈ X.coveredBase.carrier := ⟨p,rfl⟩

theorem fibre_eq_of_mem (X : RVRefinementFrame A) (p : X.base) :
    vfFibre X.base.carrier p.val.2=vfFibre A.carrier (p.val.2 ∘ X.labels) := by
  cases X.fibres p.val.2 with
  | inl he => exact False.elim (by have hp := p.property; change p.val.1 ∈ vfFibre X.base.carrier p.val.2 at hp; rw [he] at hp; exact hp)
  | inr he => exact he

theorem coveredBase_fibre_of_mem (X : RVRefinementFrame A) (p : X.base) :
    vfFibre X.coveredBase.carrier (p.val.2 ∘ X.labels)=
      vfFibre A.carrier (p.val.2 ∘ X.labels) := by
  apply Set.Subset.antisymm
  · intro a ha
    exact X.coveredBase_subset ha
  · intro a ha
    have hp : (a,p.val.2) ∈ X.base.carrier := (Set.ext_iff.mp (X.fibre_eq_of_mem p) a).mpr ha
    exact ⟨⟨(a,p.val.2),hp⟩,rfl⟩

def coveredFrame (X : RVRefinementFrame A) : RVRefinementFrame X.coveredBase := by
  refine ⟨X.arity,X.base,X.labels,X.proper,X.doublyBounded,?_⟩
  intro u
  cases X.fibres u with
  | inl he => exact Or.inl he
  | inr he =>
    right
    apply Set.Subset.antisymm
    · intro a ha
      exact ⟨⟨(a,u),ha⟩,rfl⟩
    · intro a ha
      exact (Set.ext_iff.mp he a).mpr (X.coveredBase_subset ha)

theorem coveredBase_doublyBounded (X : RVRefinementFrame A) :
    VFDoublyBounded X.coveredBase.carrier := by
  obtain ⟨γ,hγ⟩ := X.doublyBounded
  refine ⟨γ,?_⟩
  rintro q ⟨p,rfl⟩ i
  exact hγ p.val p.property i

theorem coveredBase_rvDoublyBounded (X : RVRefinementFrame A) :
    RVSupportDoublyBounded X.coveredBase.carrier := by
  obtain ⟨γ,hγ⟩ := X.proper.rvBounded
  refine ⟨γ,?_⟩
  rintro q ⟨p,rfl⟩ i
  exact hγ p.val p.property (X.labels i)

theorem coveredBase_rvPullback (X : RVRefinementFrame A) (hC : IsRVPullback X.base.carrier) :
    IsRVPullback X.coveredBase.carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro p hp
  obtain ⟨q,hq,hVF,hRV⟩ := (mem_rvHull_iff _ p).mp hp
  obtain ⟨c,hc⟩ := hq
  have hVF' : tupleRV M c.val.1=tupleRV M p.1 := by
    have he : c.val.1=q.1 := congrArg Prod.fst hc
    exact he.symm ▸ hVF
  have hTags : c.val.2 ∘ X.labels=p.2 := (congrArg Prod.snd hc).trans hRV
  have hc' : (p.1,c.val.2) ∈ X.base.carrier := rvPullback_mem_of_sameRV hC c.property hVF' rfl
  exact ⟨⟨(p.1,c.val.2),hc'⟩,Prod.ext rfl hTags⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem coveredBase_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : RVRefinementFrame A) (hC : IsRVPullback X.base.carrier) :
    ProperInvariant S X.coveredBase.carrier :=
  doublyBounded_rvPullback_properInvariant h00 hc hκ hs hv X.coveredBase X.coveredBase_doublyBounded
    X.coveredBase_rvDoublyBounded (X.coveredBase_rvPullback hC)

end DiamondIntegral.Section6.RVRefinementFrame
