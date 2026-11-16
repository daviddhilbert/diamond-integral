import «section 6».CarriedFiniteChains

/-! Actual original-base partition pieces inside a label refinement.
Their complete VF fibers are intersections with the old piece. A
proper old piece yields a proper refined piece; a prepared old piece
yields a prepared carried bundle. -/

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

def CarriedRefinementFrame.selectedPiece (X : CarriedRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) : DefSet (rawMixedSpace (M := M) n X.arity) S :=
  ⟨{p | ∃ q : X.base, q.val = p ∧ (selectRVLabelsMap X.base X.labels q).val ∈ P.carrier},
    Map.definable_preimage (selectRVLabelsMap X.base X.labels) P.definable⟩

theorem CarriedRefinementFrame.mem_selectedPiece (X : CarriedRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) (p : Mixed M n X.arity) :
    p ∈ (X.selectedPiece P).carrier ↔ p ∈ X.base.carrier ∧ (p.1,p.2 ∘ X.labels) ∈ P.carrier := by
  constructor
  · rintro ⟨q,rfl,hq⟩
    exact ⟨q.property,hq⟩
  · rintro ⟨hp,hq⟩
    exact ⟨⟨p,hp⟩,rfl,hq⟩

theorem CarriedRefinementFrame.selectedPiece_fibre (X : CarriedRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) (u : Fin X.arity → RVInfinity M) :
    vfFibre (X.selectedPiece P).carrier u = vfFibre X.base.carrier u ∩ vfFibre P.carrier (u ∘ X.labels) := by
  ext a
  exact X.mem_selectedPiece P (a,u)

theorem CarriedRefinementFrame.selectedPiece_fibres (X : CarriedRefinementFrame A)
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

theorem CarriedRefinementFrame.selectedPiece_doublyBounded (X : CarriedRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) : VFDoublyBounded (X.selectedPiece P).carrier := by
  obtain ⟨γ,hγ⟩ := X.doublyBounded
  exact ⟨γ,fun p hp i => hγ p ((X.mem_selectedPiece P p).mp hp).1 i⟩

theorem CarriedRefinementFrame.selectedPiece_bundle_mem (X : CarriedRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) (p : Mixed M (n+1) X.arity) :
    p ∈ (rvCoordinateBundle (X.selectedPiece P) X.freeLabel).carrier ↔
      p ∈ X.bundle.carrier ∧ (Fin.init p.1,p.2 ∘ X.labels) ∈ P.carrier := by
  constructor
  · rintro ⟨hp,hTag⟩
    obtain ⟨hBase,hP⟩ := (X.mem_selectedPiece P (Fin.init p.1,p.2)).mp hp
    exact ⟨⟨hBase,hTag⟩,hP⟩
  · rintro ⟨⟨hBase,hTag⟩,hP⟩
    exact ⟨(X.mem_selectedPiece P (Fin.init p.1,p.2)).mpr ⟨hBase,hP⟩,hTag⟩

theorem CarriedRefinementFrame.selectedPiece_bundle_pullback (X : CarriedRefinementFrame A)
    (P : DefSet (rawMixedSpace (M := M) n r) S) (hPA : P.carrier ⊆ A.carrier)
    (hP : IsRVPullback P.carrier) :
    IsRVPullback (rvCoordinateBundle (X.selectedPiece P) X.freeLabel).carrier :=
  rvCoordinateBundle_pullback _ _
    (labelRefinement_pullback P (X.selectedPiece P) X.labels (X.selectedPiece_fibres P hPA) hP)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CarriedRefinementFrame.selectedPiece_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : CarriedRefinementFrame A) (P : DefSet (rawMixedSpace (M := M) n r) S)
    (hP : ProperInvariant S P.carrier) : ProperInvariant S (X.selectedPiece P).carrier := by
  have hsub : (X.selectedPiece P).carrier ⊆ X.base.carrier := fun p hp => ((X.mem_selectedPiece P p).mp hp).1
  apply (lemma_6_5 h00 hc hκ hs hv _ (X.selectedPiece P).definable
    (X.proper.vfBounded.mono hsub) (X.proper.rvBounded.mono hsub)).mpr
  intro u
  rw [X.selectedPiece_fibre]
  exact (X.proper.clopen_fibres hv u).inter (hP.clopen_fibres hv (u ∘ X.labels))

def CarriedRefinementFrame.pieceFrame
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : CarriedRefinementFrame A) (P : DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : P.carrier ⊆ A.carrier) (hP : ProperInvariant S P.carrier) : CarriedRefinementFrame P :=
  ⟨X.arity,X.selectedPiece P,X.labels,X.freeLabel,
    X.selectedPiece_properInvariant h00 hc hκ hs hv P hP,
    X.selectedPiece_doublyBounded P,X.selectedPiece_fibres P hPA⟩

end DiamondIntegral.Section6
