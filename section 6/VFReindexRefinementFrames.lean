import «section 6».ReindexedRegularizationFibres
import «section 6».RVRefinementPieces

/-! A coordinate-permuted old ambient with a refinement by retained
RV labels. The actual new operations are permitted components and
regularizations; the VF permutation records their commuting square. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}

structure VFReindexRefinementFrame (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Fin n ≃ Fin n) where
  data : RVRefinementFrame (reindexedVFSet A e)

namespace VFReindexRefinementFrame
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {e : Fin n ≃ Fin n}

def oldPoint (X : VFReindexRefinementFrame A e) (p : X.data.base) : A :=
  ⟨reindexVFPoint e.symm (X.data.oldPoint p).val,
    (mem_reindexedVFSet A e (X.data.oldPoint p).val).mp (X.data.oldPoint p).property⟩

def selectedPiece (X : VFReindexRefinementFrame A e) (P : DefSet (rawMixedSpace (M := M) n r) S) :=
  X.data.selectedPiece (reindexedVFSet P e)

theorem mem_selectedPiece (X : VFReindexRefinementFrame A e)
    (P : DefSet (rawMixedSpace (M := M) n r) S) (p : Mixed M n X.data.arity) :
    p ∈ (X.selectedPiece P).carrier ↔
      p ∈ X.data.base.carrier ∧ (p.1 ∘ e.symm,p.2 ∘ X.data.labels) ∈ P.carrier := by
  rw [selectedPiece,X.data.mem_selectedPiece]
  exact and_congr Iff.rfl (mem_reindexedVFSet P e (p.1,p.2 ∘ X.data.labels))

theorem selectedPiece_subset (X : VFReindexRefinementFrame A e)
    (P : DefSet (rawMixedSpace (M := M) n r) S) :
    (X.selectedPiece P).carrier ⊆ X.data.base.carrier := X.data.selectedPiece_subset _

theorem selectedPiece_doublyBounded (X : VFReindexRefinementFrame A e)
    (P : DefSet (rawMixedSpace (M := M) n r) S) : VFDoublyBounded (X.selectedPiece P).carrier :=
  X.data.selectedPiece_doublyBounded (reindexedVFSet P e)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def portComponent (X : VFReindexRefinementFrame A e) (D : CentripetalData (G := G) A) :
    CentripetalData (G := G) X.data.base := X.data.portComponent (D.reindexVF e)

def afterCentripetal
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : VFReindexRefinementFrame A e) (D : CentripetalData (G := G) A) :
    VFReindexRefinementFrame D.map.image e := by
  let Y := X.data.afterCentripetal h00 hc hκ hs hv (D.reindexVF e)
  refine ⟨⟨Y.arity,Y.base,Y.labels,Y.proper,Y.doublyBounded,?_⟩⟩
  intro u
  cases Y.fibres u with
  | inl h => exact Or.inl h
  | inr h =>
    exact Or.inr (h.trans (congrArg (fun V : Set (Mixed M n (1+r)) => vfFibre V (u ∘ Y.labels))
      (congrArg DefSet.carrier (D.reindexVF_image e))))

def afterRegularization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : VFReindexRefinementFrame A e) : VFReindexRefinementFrame (regularizeMap A).image e := by
  refine ⟨⟨n+X.data.arity,(regularizeMap X.data.base).image,
    regularizedLabelSelection n X.data.labels ∘ regularizedVFPermutationLabels e,
    regularization_properInvariant h00 hc hκ hs hv X.data.base X.data.proper X.data.doublyBounded,
    regularized_vfDoublyBounded X.data.doublyBounded,?_⟩⟩
  intro u
  cases labelRefinement_regularization (reindexedVFSet A e) X.data.base X.data.labels X.data.fibres u with
  | inl h => exact Or.inl h
  | inr h =>
    right
    exact h.trans (reindexed_regularization_fibres A e (u ∘ regularizedLabelSelection n X.data.labels))

theorem selectedPiece_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : VFReindexRefinementFrame A e) (P : DefSet (rawMixedSpace (M := M) n r) S)
    (hP : ProperInvariant S P.carrier) : ProperInvariant S (X.selectedPiece P).carrier :=
  X.data.selectedPiece_properInvariant h00 hc hκ hs hv _ (reindexedVFSet_properInvariant P e hP)

end VFReindexRefinementFrame
end DiamondIntegral.Section6
