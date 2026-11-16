import «section 6».SynchronizedTagChainExtensions

/-! A branch extension preserves preparation of every RV-pullback
outside that branch. The proof uses the actual inverse point, retained
old labels and the VF identity on the complementary branch. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
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

theorem SynchronizedTagBranchExtension.outside_image_rvPullback
    (h00 : M ⊨ Axioms.ACVF00) {X : SynchronizedTagBranchFrame C Q}
    (F : SynchronizedTagBranchExtension (G := G) X f hQC)
    (hA : IsRVPullback X.ambient.carrier)
    (R : DefSet (rawMixedSpace (M := M) n r) S) (hRA : R.carrier ⊆ X.ambient.carrier)
    (hR : IsRVPullback R.carrier) (hOut : ∀ x ∈ R.carrier,x.2 ∉ X.tags.carrier) :
    IsRVPullback (F.map.restrict hRA).image.carrier := by
  have hTarget := F.chain.toChain.target_rvPullback h00 hA
  obtain ⟨hrs,hRetain⟩ := F.chain.toChain.toSpecial.retainsRV
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro y hy
  obtain ⟨x,hx,hVF,hRV⟩ := (mem_rvHull_iff _ y).mp hy
  obtain ⟨a,ha⟩ := hx
  let aA : X.ambient := ⟨a.val,hRA a.property⟩
  have haV : (F.map aA).val=x := ha
  have hxTarget : x ∈ F.output.ambient.carrier := ha ▸ (F.map aA).property
  have hyTarget : y ∈ F.output.ambient.carrier := rvPullback_mem_of_sameRV hTarget hxTarget hVF hRV
  obtain ⟨b,hb⟩ := (F.chain.toChain.toSpecial.bijective h00).surjective ⟨y,hyTarget⟩
  have hbV : (F.map b).val=y := congrArg Subtype.val hb
  have hau : aA.val.2 ∉ X.tags.carrier := hOut a.val a.property
  have hbu : b.val.2 ∉ X.tags.carrier := by
    intro h
    have hLabel : (F.map aA).val.2=(F.map b).val.2 := by rw [haV,hbV]; exact hRV
    have hSelected := (F.selected b).mpr h
    rw [← hLabel] at hSelected
    exact hau ((F.selected aA).mp hSelected)
  have hOld : a.val.2=b.val.2 := by
    funext i
    rw [← hRetain aA i,← hRetain b i,haV,hbV,hRV]
  have hValue : tupleRV M a.val.1=tupleRV M b.val.1 := by
    rw [← F.outside aA hau,← F.outside b hbu,haV,hbV]
    exact hVF
  have hbR : b.val ∈ R.carrier := rvPullback_mem_of_sameRV hR a.property hValue hOld
  exact ⟨⟨b.val,hbR⟩,hbV⟩

end DiamondIntegral.Section6
