import «section 6».TagBranchOutsidePullbacks
import «section 6».PreparedSynchronizedFamilies
import Section4.RVRestrictions

/-! A prepared selected branch completes preparation when its
complement is already prepared. Full protected-set identities and
outside preservation give the actual global synchronized witness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {C : DefSet (rawMixedSpace (M := M) n r) S}
variable {Q : Fin k → DefSet (rawMixedSpace (M := M) n r) S}
variable {B : DefSet (rawMixedSpace (M := M) n s) S} {f : Map C B}
variable {hQC : ∀ i,(Q i).carrier ⊆ C.carrier}

theorem SynchronizedTagBranchExtension.prepared_of_branch_and_complement
    (h00 : M ⊨ Axioms.ACVF00) {X : SynchronizedTagBranchFrame C Q}
    (F : SynchronizedTagBranchExtension (G := G) X f hQC)
    (hA : IsRVPullback X.ambient.carrier)
    (hPrepared : ∀ i,IsRVPullback (f.restrict (hQC i)).image.carrier)
    (hComplement : ∀ i,IsRVPullback
      ((X.pieces i).sdiff (focusActive (X.pieces i) X.tags)).carrier) :
    ∀ i,IsRVPullback (F.output.pieces i).carrier := by
  intro i
  let R := (X.pieces i).sdiff (focusActive (X.pieces i) X.tags)
  have hRA : R.carrier ⊆ X.ambient.carrier := fun _ hx => X.pieces_subset i hx.1
  have hROut : ∀ x ∈ R.carrier,x.2 ∉ X.tags.carrier := by
    intro x hx hu
    exact hx.2 ⟨hx.1,hu⟩
  have hRImage := F.outside_image_rvPullback h00 hA R hRA (hComplement i) hROut
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro y hy
  obtain ⟨x,hx,hVF,hRV⟩ := (mem_rvHull_iff _ y).mp hy
  by_cases hu : x.2 ∈ F.output.tags.carrier
  · have hSelected : x ∈ (f.restrict (hQC i)).image.carrier := by
      rw [F.output.pieces_eq i]
      exact ⟨hx,hu⟩
    have hY := rvPullback_mem_of_sameRV (hPrepared i) hSelected hVF hRV
    rw [F.output.pieces_eq i] at hY
    exact hY.1
  · have hxImage : x ∈ (F.map.restrict (X.pieces_subset i)).image.carrier := by
      simpa only [F.piece_images i] using hx
    obtain ⟨a,ha⟩ := hxImage
    let aA : X.ambient := ⟨a.val,X.pieces_subset i a.property⟩
    have hau : a.val.2 ∉ X.tags.carrier := by
      intro h
      apply hu
      rw [← ha]
      exact (F.selected aA).mpr h
    have haR : a.val ∈ R.carrier := ⟨a.property,fun h => hau h.2⟩
    have hxR : x ∈ (F.map.restrict hRA).image.carrier := ⟨⟨a.val,haR⟩,ha⟩
    have hyR := rvPullback_mem_of_sameRV hRImage hxR hVF hRV
    obtain ⟨b,hb⟩ := hyR
    rw [F.piece_images i]
    exact ⟨⟨b.val,b.property.1⟩,hb⟩

def SynchronizedTagBranchExtension.preparedFamily
    (h00 : M ⊨ Axioms.ACVF00) {X : SynchronizedTagBranchFrame C Q}
    (F : SynchronizedTagBranchExtension (G := G) X f hQC)
    (hA : IsRVPullback X.ambient.carrier)
    (hPrepared : ∀ i,IsRVPullback (f.restrict (hQC i)).image.carrier)
    (hComplement : ∀ i,IsRVPullback
      ((X.pieces i).sdiff (focusActive (X.pieces i) X.tags)).carrier) :
    PreparedSynchronizedFamily (G := G) X.ambient X.pieces X.pieces_subset := {
  arity := s
  target := F.output.ambient
  map := F.map
  chain := F.chain
  proper := F.output.proper
  doublyBounded := F.output.doublyBounded
  pullback := F.chain.toChain.target_rvPullback h00 hA
  prepared := fun i => by
    rw [← F.piece_images i]
    exact F.prepared_of_branch_and_complement h00 hA hPrepared hComplement i }

end DiamondIntegral.Section6
