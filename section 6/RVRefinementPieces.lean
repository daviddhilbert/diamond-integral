import «section 6».RVRefinementFrames

/-! Actual protected pieces inside ordinary RV-label refinements. Their
full fibres, properness and double bounds remain over the original base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

def RVRefinementFrame.selectedPiece (X : RVRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) : DefSet (rawMixedSpace (M := M) n X.arity) S :=
  ⟨{p | ∃ q : X.base, q.val = p ∧ (selectRVLabelsMap X.base X.labels q).val ∈ P.carrier},
    Map.definable_preimage (selectRVLabelsMap X.base X.labels) P.definable⟩

theorem RVRefinementFrame.mem_selectedPiece (X : RVRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) (p : Mixed M n X.arity) :
    p ∈ (X.selectedPiece P).carrier ↔ p ∈ X.base.carrier ∧ (p.1,p.2 ∘ X.labels) ∈ P.carrier := by
  constructor
  · rintro ⟨q,rfl,hq⟩
    exact ⟨q.property,hq⟩
  · rintro ⟨hp,hq⟩
    exact ⟨⟨p,hp⟩,rfl,hq⟩

theorem RVRefinementFrame.selectedPiece_fibre (X : RVRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) (u : Fin X.arity → RVInfinity M) :
    vfFibre (X.selectedPiece P).carrier u = vfFibre X.base.carrier u ∩ vfFibre P.carrier (u ∘ X.labels) := by
  ext a
  exact X.mem_selectedPiece P (a,u)

theorem RVRefinementFrame.selectedPiece_fibres (X : RVRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) (hPA : P.carrier ⊆ A.carrier)
    (u : Fin X.arity → RVInfinity M) :
    vfFibre (X.selectedPiece P).carrier u = ∅ ∨
      vfFibre (X.selectedPiece P).carrier u = vfFibre P.carrier (u ∘ X.labels) := by
  rw [X.selectedPiece_fibre]
  cases X.fibres u with
  | inl he => left; rw [he,Set.empty_inter]
  | inr he =>
    right
    rw [he]
    exact Set.inter_eq_right.mpr (fun a ha => hPA ha)

theorem RVRefinementFrame.selectedPiece_doublyBounded (X : RVRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) : VFDoublyBounded (X.selectedPiece P).carrier := by
  obtain ⟨γ,hγ⟩ := X.doublyBounded
  exact ⟨γ,fun p hp i => hγ p ((X.mem_selectedPiece P p).mp hp).1 i⟩

theorem RVRefinementFrame.selectedPiece_subset (X : RVRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) :
    (X.selectedPiece P).carrier ⊆ X.base.carrier :=
  fun p hp => ((X.mem_selectedPiece P p).mp hp).1

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem RVRefinementFrame.selectedPiece_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : RVRefinementFrame A) (P : DefSet (rawMixedSpace (M := M) n r) S)
    (hP : ProperInvariant S P.carrier) : ProperInvariant S (X.selectedPiece P).carrier := by
  have hsub : (X.selectedPiece P).carrier ⊆ X.base.carrier := fun p hp => ((X.mem_selectedPiece P p).mp hp).1
  apply (lemma_6_5 h00 hc hκ hs hv _ (X.selectedPiece P).definable
    (X.proper.vfBounded.mono hsub) (X.proper.rvBounded.mono hsub)).mpr
  intro u
  rw [X.selectedPiece_fibre]
  exact (X.proper.clopen_fibres hv u).inter (hP.clopen_fibres hv (u ∘ X.labels))

def RVRefinementFrame.pieceFrame
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : RVRefinementFrame A) (P : DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : P.carrier ⊆ A.carrier) (hP : ProperInvariant S P.carrier) : RVRefinementFrame P :=
  ⟨X.arity,X.selectedPiece P,X.labels,
    X.selectedPiece_properInvariant h00 hc hκ hs hv P hP,
    X.selectedPiece_doublyBounded P,X.selectedPiece_fibres P hPA⟩

end DiamondIntegral.Section6
