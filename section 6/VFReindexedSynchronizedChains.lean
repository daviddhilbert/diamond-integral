import «section 6».VFReindexedChainLifts
import «section 6».RVRefinementSynchronizedChains

/-! Whole synchronized chains transport through a VF coordinate
permutation and retained-label refinement, using literal permitted
operations with exact full protected images at every composition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ} {I : Type*}
variable {e : Fin n ≃ Fin n}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem VFReindexRefinementFrame.portComponent_commutes
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : VFReindexRefinementFrame A e)
    (D : CentripetalData (G := G) A) (p : X.data.base) :
    ((X.portComponent D).point p.val).1 ∘ e.symm=(D.point (X.oldPoint p).val).1 ∧
      ((X.portComponent D).point p.val).2 ∘ prefixLabelSelection X.data.labels=
        (D.point (X.oldPoint p).val).2 := by
  have hPort := (D.reindexVF e).refineLabels_point_commutes X.data.labels X.data.proper X.data.doublyBounded
    (labelRefinement_tagged _ _ _ X.data.fibres (D.reindexVF e).tagged) X.data.fibres p.val p.property
  have hInv : reindexVFPoint e (X.oldPoint p).val=(X.data.oldPoint p).val := by
    change reindexVFPoint e (reindexVFPoint e.symm (X.data.oldPoint p).val)=(X.data.oldPoint p).val
    simpa only [Equiv.symm_symm] using reindexVFPoint_inverse e.symm (X.data.oldPoint p).val
  have hOld := D.reindexVF_point e (X.oldPoint p).val (X.oldPoint p).property
  rw [hInv] at hOld
  have h := (congrArg (reindexVFPoint e.symm) (hPort.trans hOld)).trans
    (reindexVFPoint_inverse e (D.point (X.oldPoint p).val))
  exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩

def VFReindexedChainLift.centripetal
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : VFReindexRefinementFrame A e)
    (D : CentripetalData (G := G) A) (P : I → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (E : ∀ i,CentripetalData (G := G) (P i))
    (hData : ∀ i,ApertureRestrictionData D (E i)) : VFReindexedChainLift (G := G) X D.bijection P where
  target := X.afterCentripetal h00 hc hκ hs hv D
  map := (X.portComponent D).bijection
  chain := .centripetal X.data.base (X.portComponent D) _ (fun i => X.selectedPiece_subset (P i))
    (fun i => (X.data.pieceFrame h00 hc hκ hs hv (reindexedVFSet (P i) e)
      ((hData i).reindexVF e).subset ((E i).reindexVF e).sourceProper).portComponent ((E i).reindexVF e))
    (fun i => X.data.portComponent_restriction_data h00 hc hκ hs hv (D.reindexVF e) ((E i).reindexVF e)
      ((hData i).reindexVF e).subset ((hData i).reindexVF e))
  commutes p := Prod.ext (X.portComponent_commutes D p).1 (X.portComponent_commutes D p).2

theorem SynchronizedCentripetalChain.vf_reindexed_lift_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SynchronizedCentripetalChain (G := G) I A B f P) :
    ∀ X : VFReindexRefinementFrame A e,Nonempty (VFReindexedChainLift (G := G) X f P) := by
  induction h with
  | identity A hA P hPA hP =>
    intro X
    exact ⟨VFReindexedChainLift.identity h00 hc hκ hs hv X P hP⟩
  | regularize A hA hVF P hPA hP hPVF =>
    intro X
    exact ⟨VFReindexedChainLift.regularize h00 hc hκ hs hv X P hP⟩
  | centripetal A D P hPA E hData =>
    intro X
    exact ⟨VFReindexedChainLift.centripetal h00 hc hκ hs hv X D P hPA E hData⟩
  | comp P hPA hf hg ihf ihg =>
    intro X
    obtain ⟨F⟩ := ihf X
    obtain ⟨H⟩ := ihg F.target
    exact ⟨F.comp h00 (hf.toChain.toSpecial.bijective h00).injective hPA H⟩

theorem PreparedSynchronizedFamily.refine_vf_coordinates
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S} {hPA : ∀ i,(P i).carrier ⊆ A.carrier}
    (F : PreparedSynchronizedFamily (G := G) A P hPA) (X : VFReindexRefinementFrame A e) :
    Nonempty (PreparedSynchronizedFamily (G := G) X.data.base (fun i => X.selectedPiece (P i))
      (fun i => X.selectedPiece_subset (P i))) := by
  obtain ⟨K⟩ := F.chain.vf_reindexed_lift_exists h00 hc hκ hs hv X
  refine ⟨⟨K.target.data.arity,K.target.data.base,K.map,K.chain,K.target.data.proper,K.target.data.doublyBounded,
    K.target.data.pullback (reindexedVFSet_rvPullback F.target e F.pullback),fun i => ?_⟩⟩
  rw [K.partition_image h00 (F.chain.toChain.toSpecial.bijective h00).injective i (hPA i)]
  apply labelRefinement_pullback (reindexedVFSet (F.map.restrict (hPA i)).image e)
    (K.target.data.selectedPiece (reindexedVFSet (F.map.restrict (hPA i)).image e)) K.target.data.labels
    (K.target.data.selectedPiece_fibres _ ?_) (reindexedVFSet_rvPullback _ e (F.prepared i))
  intro q hq
  apply (mem_reindexedVFSet F.target e q).mpr
  obtain ⟨p,hp⟩ := (mem_reindexedVFSet (F.map.restrict (hPA i)).image e q).mp hq
  exact hp ▸ (F.map.restrict (hPA i) p).property

end DiamondIntegral.Section6
