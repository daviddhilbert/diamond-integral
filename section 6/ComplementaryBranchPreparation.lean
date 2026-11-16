import «section 6».OutsideBranchRefinements

/-! Actual preparations on two complementary retained-label branches
assemble to one permitted synchronized preparation of the whole source.
Full protected images are retained throughout both branch extensions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem synchronized_preparation_glue_complementary_tags
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) (hRP : IsRVPullback A.carrier)
    (hTag : ∀ p ∈ A.carrier,∀ z ∈ A.carrier,p.2=z.2 → tupleRV M p.1=tupleRV M z.1)
    (P : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (hP : ∀ i,ProperInvariant S (P i).carrier)
    (U : DefSet (rawRVSpace (M := M) r) S)
    (F : PreparedSynchronizedFamily (G := G) (focusActive A U) (fun i => focusActive (P i) U)
      (fun i _ hp => ⟨hPA i hp.1,hp.2⟩))
    (G' : PreparedSynchronizedFamily (G := G) (focusActive A (rvTagComplement U))
      (fun i => focusActive (P i) (rvTagComplement U)) (fun i _ hp => ⟨hPA i hp.1,hp.2⟩)) :
    Nonempty (PreparedSynchronizedFamily (G := G) A P hPA) := by
  let F' := F.taggedTarget h00 hc hκ hs hv
  let X := SynchronizedTagBranchFrame.of_slice A P hPA hA hD hP hTag U
  obtain ⟨E⟩ := F'.chain.tag_branch_extension h00 hc hκ hs hv X
  have hBRP := E.chain.toChain.target_rvPullback h00 hRP
  have hBTag := E.output.tagged_of_local (F.taggedTarget_tagged h00 hc hκ hs hv)
  obtain ⟨G₀⟩ := G'.refine_rv_labels h00 hc hκ hs hv (E.outsideFrame h00 hRP hTag)
  have hGPieces := fun i => E.outsideFrame_piece h00 hRP hTag i
  let G₁ : PreparedSynchronizedFamily (G := G) (focusActive E.output.ambient (rvTagComplement E.output.tags))
      (fun i => focusActive (E.output.pieces i) (rvTagComplement E.output.tags))
      (fun i _ hp => ⟨E.output.pieces_subset i hp.1,hp.2⟩) := G₀.changePieces hGPieces
  let Y := SynchronizedTagBranchFrame.of_slice E.output.ambient E.output.pieces E.output.pieces_subset
    E.output.proper E.output.doublyBounded E.output.pieces_proper hBTag (rvTagComplement E.output.tags)
  obtain ⟨H⟩ := G₁.chain.tag_branch_extension h00 hc hκ hs hv Y
  have hComplement (i) : IsRVPullback
      ((Y.pieces i).sdiff (focusActive (Y.pieces i) Y.tags)).carrier := by
    have he : ((Y.pieces i).sdiff (focusActive (Y.pieces i) Y.tags)).carrier=
        (focusActive (E.output.pieces i) E.output.tags).carrier := by
      ext z
      change (z ∈ (E.output.pieces i).carrier ∧
        ¬ (z ∈ (E.output.pieces i).carrier ∧ z.2 ∉ E.output.tags.carrier)) ↔
          (z ∈ (E.output.pieces i).carrier ∧ z.2 ∈ E.output.tags.carrier)
      tauto
    rw [he]
    exact (E.output.pieces_eq i) ▸ F'.prepared i
  let J := H.preparedFamily h00 hBRP G₁.prepared hComplement
  let J' : PreparedSynchronizedFamily (G := G) E.output.ambient
      (fun i => (E.map.restrict (hPA i)).image)
      (fun i z hz => by obtain ⟨p,hp⟩ := hz; exact hp ▸ (E.map.restrict (hPA i) p).property) :=
    J.changePieces (fun i => E.piece_images i)
  exact ⟨J'.precompose hPA E.chain⟩

end DiamondIntegral.Section6
