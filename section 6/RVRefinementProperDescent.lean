import «section 6».RVRefinementCoveredBases

/-! Proper protected sets descend to the portion of the old ambient
actually covered by a label refinement. Each inhabited old fibre is one
entire new fibre, so clopenness descends before applying the named criterion. -/

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

def coveredPiece (X : RVRefinementFrame A) (Q : DefSet (rawMixedSpace (M := M) n r) S) :
    DefSet (rawMixedSpace (M := M) n r) S :=
  ⟨Q.carrier ∩ X.coveredBase.carrier,Q.definable.inter _ X.coveredBase.definable⟩

theorem coveredPiece_fibre (X : RVRefinementFrame A) (Q : DefSet (rawMixedSpace (M := M) n r) S)
    (u : Fin r → RVInfinity M) :
    vfFibre (X.coveredPiece Q).carrier u=vfFibre Q.carrier u ∩ vfFibre X.coveredBase.carrier u := by
  ext a
  rfl

theorem selected_coveredPiece_eq (X : RVRefinementFrame A) (Q : DefSet (rawMixedSpace (M := M) n r) S) :
    X.coveredFrame.selectedPiece (X.coveredPiece Q)=X.selectedPiece Q := by
  apply defSet_eq_of_carrier_eq
  ext p
  rw [X.coveredFrame.mem_selectedPiece,X.mem_selectedPiece]
  constructor
  · rintro ⟨hp,hQ,hL⟩
    exact ⟨hp,hQ⟩
  · rintro ⟨hp,hQ⟩
    exact ⟨hp,hQ,X.source_subset_covered ⟨p,hp⟩⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem coveredPiece_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : RVRefinementFrame A) (hC : IsRVPullback X.base.carrier)
    (Q : DefSet (rawMixedSpace (M := M) n r) S)
    (hQ : ProperInvariant S (X.selectedPiece Q).carrier) :
    ProperInvariant S (X.coveredPiece Q).carrier := by
  have hL := X.coveredBase_properInvariant h00 hc hκ hs hv hC
  have hSub : (X.coveredPiece Q).carrier ⊆ X.coveredBase.carrier := fun _ hp => hp.2
  apply (lemma_6_5 h00 hc hκ hs hv _ (X.coveredPiece Q).definable
    (hL.vfBounded.mono hSub) (hL.rvBounded.mono hSub)).mpr
  intro u
  by_cases hNonempty : (vfFibre X.coveredBase.carrier u).Nonempty
  · obtain ⟨a,ha⟩ := hNonempty
    obtain ⟨c,hc⟩ := ha
    have hTags : c.val.2 ∘ X.labels=u := congrArg Prod.snd hc
    have hCovered := X.coveredBase_fibre_of_mem c
    rw [hTags] at hCovered
    have hSelected := X.selectedPiece_fibre Q c.val.2
    rw [X.fibre_eq_of_mem c,hTags] at hSelected
    have he : vfFibre (X.coveredPiece Q).carrier u=vfFibre (X.selectedPiece Q).carrier c.val.2 := by
      rw [X.coveredPiece_fibre,hCovered,hSelected,Set.inter_comm]
    rw [he]
    exact hQ.clopen_fibres hv c.val.2
  · have he : vfFibre X.coveredBase.carrier u=∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun a ha => hNonempty ⟨a,ha⟩)
    rw [X.coveredPiece_fibre,he,Set.inter_empty]
    exact isClopen_empty

end DiamondIntegral.Section6.RVRefinementFrame
