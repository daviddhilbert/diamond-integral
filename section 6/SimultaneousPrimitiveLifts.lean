import «section 6».SimultaneousCarriedLifts

/-! Primitive carried lifts with all protected restrictions checked
against one ambient map. The permitted narrow components come from
the corresponding old component data on each original piece. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def SimultaneousCarriedLift.identity
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (P : I → DefSet (rawMixedSpace (M := M) n r) S)
    (hP : ∀ i, ProperInvariant S (P i).carrier) : SimultaneousCarriedLift (G := G) X (Map.id A) P := by
  let F := CarriedChainLift.identity h00 hc hκ hs hv X
  refine ⟨F,fun i => ?_⟩
  let R := rvCoordinateBundle (X.selectedPiece (P i)) X.freeLabel
  have hR : ProperInvariant S R.carrier := rvCoordinateBundle_properInvariant h00 hc hκ hs hv
    (X.selectedPiece (P i)) X.freeLabel (X.selectedPiece_properInvariant h00 hc hκ hs hv (P i) (hP i))
  exact (SpecialCovariantChain.identity R hR).restriction_of_liesOver
    h00 F.map (X.selectedPiece_bundle_subset (P i)) (fun _ => rfl)

def SimultaneousCarriedLift.regularize
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (P : I → DefSet (rawMixedSpace (M := M) n r) S)
    (hP : ∀ i, ProperInvariant S (P i).carrier) : SimultaneousCarriedLift (G := G) X (regularization A) P := by
  let F := CarriedChainLift.regularize h00 hc hκ hs hv X
  refine ⟨F,fun i => ?_⟩
  let R := rvCoordinateBundle (X.selectedPiece (P i)) X.freeLabel
  have hBase := X.selectedPiece_properInvariant h00 hc hκ hs hv (P i) (hP i)
  have hR : ProperInvariant S R.carrier := rvCoordinateBundle_properInvariant h00 hc hκ hs hv
    (X.selectedPiece (P i)) X.freeLabel hBase
  have hDouble : VFDoublyBounded R.carrier := rvCoordinateBundle_doublyBounded
    (X.selectedPiece (P i)) X.freeLabel (X.selectedPiece_doublyBounded (P i)) hBase.rvBounded
  apply (SpecialCovariantChain.regularize R hR hDouble).restriction_of_liesOver
    h00 F.map (X.selectedPiece_bundle_subset (P i))
  intro p
  have he : (F.map ⟨p.val,X.selectedPiece_bundle_subset (P i) p.property⟩).val =
      DiamondIntegral.Section6.regularize p.val := changeMapTarget_value _ _ _
  exact he.symm

def SimultaneousCarriedLift.centripetal
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (D : CentripetalData (G := G) A) (P : I → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier) (E : ∀ i, CentripetalData (G := G) (P i))
    (hPoint : ∀ i, ∀ p ∈ (P i).carrier, (E i).point p = D.point p) :
    SimultaneousCarriedLift (G := G) X D.bijection P := by
  let F := CarriedChainLift.centripetal h00 hc hκ hs hv X D
  refine ⟨F,fun i => ?_⟩
  let Y := X.pieceFrame h00 hc hκ hs hv (P i) (hPA i) (E i).sourceProper
  let H := Y.carriedComponent h00 hc hκ hs hv (E i)
  apply (SpecialCovariantChain.centripetal Y.bundle H).restriction_of_liesOver
    h00 F.map (X.selectedPiece_bundle_subset (P i))
  intro p
  have hNarrow := X.carriedComponent_restriction_point h00 hc hκ hs hv D (P i) (hPA i)
    (E i).sourceProper (E i) (hPoint i) p.val p.property
  have hWhole : (F.map ⟨p.val,X.selectedPiece_bundle_subset (P i) p.property⟩).val =
      (X.carriedComponent h00 hc hκ hs hv D).point p.val := changeMapTarget_value _ _ _
  exact hNarrow.trans hWhole.symm

end DiamondIntegral.Section6
