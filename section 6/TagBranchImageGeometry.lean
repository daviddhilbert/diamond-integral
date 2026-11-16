import «section 6».SynchronizedTagComponentExtensions
import «section 6».RVLabelSelection

/-! Whole-label branches commute with literal protected images under
maps retaining the original labels. These full-set identities supply
the next branch domain when extending an entire finite chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}

structure SynchronizedTagBranchFrame
    (C : DefSet (rawMixedSpace (M := M) n r) S)
    (Q : Fin k → DefSet (rawMixedSpace (M := M) n r) S) where
  ambient : DefSet (rawMixedSpace (M := M) n r) S
  pieces : Fin k → DefSet (rawMixedSpace (M := M) n r) S
  tags : DefSet (rawRVSpace (M := M) r) S
  proper : ProperInvariant S ambient.carrier
  doublyBounded : VFDoublyBounded ambient.carrier
  pieces_subset : ∀ i,(pieces i).carrier ⊆ ambient.carrier
  pieces_proper : ∀ i,ProperInvariant S (pieces i).carrier
  source_eq : C.carrier=(focusActive ambient tags).carrier
  pieces_eq : ∀ i,(Q i).carrier=(focusActive (pieces i) tags).carrier
  outside_tagged : ∀ x ∈ ambient.carrier,∀ y ∈ ambient.carrier,x.2=y.2 →
    x.2 ∉ tags.carrier → tupleRV M x.1=tupleRV M y.1

namespace SynchronizedTagBranchFrame
variable {C : DefSet (rawMixedSpace (M := M) n r) S}
variable {Q : Fin k → DefSet (rawMixedSpace (M := M) n r) S}

theorem subset (X : SynchronizedTagBranchFrame C Q) : C.carrier ⊆ X.ambient.carrier := by
  intro x hx
  rw [X.source_eq] at hx
  exact hx.1

theorem local_pieces_subset (X : SynchronizedTagBranchFrame C Q) (i) : (Q i).carrier ⊆ C.carrier := by
  intro x hx
  rw [X.pieces_eq i] at hx
  rw [X.source_eq]
  exact ⟨X.pieces_subset i hx.1,hx.2⟩

theorem tagged_of_local (X : SynchronizedTagBranchFrame C Q)
    (hC : ∀ x ∈ C.carrier,∀ y ∈ C.carrier,x.2=y.2 → tupleRV M x.1=tupleRV M y.1) :
    ∀ x ∈ X.ambient.carrier,∀ y ∈ X.ambient.carrier,x.2=y.2 → tupleRV M x.1=tupleRV M y.1 := by
  intro x hx y hy hxy
  by_cases hu : x.2 ∈ X.tags.carrier
  · apply hC x (by rw [X.source_eq]; exact ⟨hx,hu⟩) y (by
      rw [X.source_eq]; exact ⟨hy,hxy ▸ hu⟩) hxy
  · exact X.outside_tagged x hx y hy hxy hu

end SynchronizedTagBranchFrame

theorem map_tag_slice_image
    {A P C : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (U : DefSet (rawRVSpace (M := M) r) S) (σ : Fin r → Fin s)
    (hRV : ∀ x : A,(f x).val.2 ∘ σ=x.val.2)
    (hPA : P.carrier ⊆ A.carrier) (hCA : C.carrier ⊆ A.carrier)
    (hC : C.carrier=(focusActive P U).carrier) :
    (f.restrict hCA).image=focusActive (f.restrict hPA).image (selectedRVTagSet U σ) := by
  apply defSet_eq_of_carrier_eq
  ext y
  constructor
  · rintro ⟨x,hx⟩
    have hSlice : x.val ∈ (focusActive P U).carrier := hC ▸ x.property
    have hxP : x.val ∈ P.carrier := hSlice.1
    have hxU : x.val.2 ∈ U.carrier := hSlice.2
    refine ⟨⟨⟨x.val,hxP⟩,hx⟩,?_⟩
    change y.2 ∘ σ ∈ U.carrier
    rw [← hx]
    exact (hRV ⟨x.val,hCA x.property⟩).symm ▸ hxU
  · rintro ⟨⟨x,hx⟩,hy⟩
    have hxU : x.val.2 ∈ U.carrier := by
      change y.2 ∘ σ ∈ U.carrier at hy
      rw [← hx] at hy
      exact (hRV ⟨x.val,hPA x.property⟩) ▸ hy
    have hxC : x.val ∈ C.carrier := by rw [hC]; exact ⟨x.property,hxU⟩
    exact ⟨⟨x.val,hxC⟩,hx⟩

theorem map_branch_image
    {A C : DefSet (rawMixedSpace (M := M) n r) S}
    {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Surjective f)
    (U : DefSet (rawRVSpace (M := M) r) S) (σ : Fin r → Fin s)
    (hRV : ∀ x : A,(f x).val.2 ∘ σ=x.val.2)
    (hCA : C.carrier ⊆ A.carrier) (hC : C.carrier=(focusActive A U).carrier) :
    (f.restrict hCA).image=focusActive B (selectedRVTagSet U σ) := by
  have h := map_tag_slice_image f U σ hRV (fun _ hx => hx) hCA hC
  have hImage : (f.restrict (fun _ hx => hx)).image=B := map_image_eq_target_of_surjective f hf
  rwa [hImage] at h

end DiamondIntegral.Section6
