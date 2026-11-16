import «section 6».CarriedPartitionImages

/-! A compatible old restriction gives a compatible carried component
on the actual refined piece. Its literal restriction is therefore a
special covariant chain, not merely a map with the correct RV image. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def CarriedRefinementFrame.carriedComponent
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (D : CentripetalData (G := G) A) : CentripetalData (G := G) X.bundle :=
  (X.portComponent D).carryCoordinate X.freeLabel
    (rvCoordinateBundle_properInvariant h00 hc hκ hs hv X.base X.freeLabel X.proper)

theorem CarriedRefinementFrame.carriedComponent_point
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (D : CentripetalData (G := G) A) (p : Mixed M (n+1) X.arity) (hp : p ∈ X.bundle.carrier) :
    (X.carriedComponent h00 hc hκ hs hv D).point p =
      (Fin.snoc (D.point (Fin.init p.1,p.2 ∘ X.labels)).1 (p.1 (Fin.last n)),
        Fin.append (fun _ : Fin 1 => (D.point (Fin.init p.1,p.2 ∘ X.labels)).2 (Fin.castAdd r 0)) p.2) := by
  let E := X.portComponent D
  have hW := rvCoordinateBundle_properInvariant h00 hc hκ hs hv X.base X.freeLabel X.proper
  change (E.carryCoordinate X.freeLabel hW).point p = _
  rw [E.carryCoordinate_point X.freeLabel hW p hp]
  have hVF := congrArg Prod.fst (D.refineLabels_point_commutes X.labels X.proper X.doublyBounded
    (labelRefinement_tagged A X.base X.labels X.fibres D.tagged) X.fibres (Fin.init p.1,p.2) hp.1)
  have hCore := D.refineLabels_core X.labels X.proper X.doublyBounded
    (labelRefinement_tagged A X.base X.labels X.fibres D.tagged) X.fibres (Fin.init p.1,p.2) hp.1
  change E.core (Fin.init p.1,p.2) = D.core (Fin.init p.1,p.2 ∘ X.labels) at hCore
  apply Prod.ext
  · exact congrArg (fun a => (Fin.snoc a (p.1 (Fin.last n)) : Fin (n+1) → VF M)) hVF
  · change Fin.append (fun _ : Fin 1 => branchTag (M := M) (E.core (Fin.init p.1,p.2))) p.2 = _
    simp only [CentripetalData.point,Fin.append_left]
    rw [hCore]

theorem CarriedRefinementFrame.carriedComponent_restriction_point
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (D : CentripetalData (G := G) A) (P : DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : P.carrier ⊆ A.carrier) (hP : ProperInvariant S P.carrier) (E : CentripetalData (G := G) P)
    (hPoint : ∀ a ∈ P.carrier, E.point a = D.point a)
    (p : Mixed M (n+1) X.arity)
    (hp : p ∈ (rvCoordinateBundle (X.selectedPiece P) X.freeLabel).carrier) :
    ((X.pieceFrame h00 hc hκ hs hv P hPA hP).carriedComponent h00 hc hκ hs hv E).point p =
      (X.carriedComponent h00 hc hκ hs hv D).point p := by
  obtain ⟨hParent,hOld⟩ := (X.selectedPiece_bundle_mem P p).mp hp
  rw [(X.pieceFrame h00 hc hκ hs hv P hPA hP).carriedComponent_point h00 hc hκ hs hv E p hp,
    X.carriedComponent_point h00 hc hκ hs hv D p hParent]
  exact congrArg (fun q : Mixed M n (1+r) =>
    ((Fin.snoc q.1 (p.1 (Fin.last n)) : Fin (n+1) → VF M),
      Fin.append (fun _ : Fin 1 => q.2 (Fin.castAdd r 0)) p.2))
      (hPoint (Fin.init p.1,p.2 ∘ X.labels) hOld)

theorem CarriedRefinementFrame.carriedComponent_restriction_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (D : CentripetalData (G := G) A) (P : DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : P.carrier ⊆ A.carrier) (hP : ProperInvariant S P.carrier) (E : CentripetalData (G := G) P)
    (hPoint : ∀ a ∈ P.carrier, E.point a = D.point a) :
    SpecialCovariantChain (G := G) (rvCoordinateBundle (X.selectedPiece P) X.freeLabel)
      ((X.carriedComponent h00 hc hκ hs hv D).bijection.restrict (X.selectedPiece_bundle_subset P)).image
      ((X.carriedComponent h00 hc hκ hs hv D).bijection.restrict (X.selectedPiece_bundle_subset P)).toImage :=
  centripetal_restriction_chain h00 (X.carriedComponent h00 hc hκ hs hv D)
    ((X.pieceFrame h00 hc hκ hs hv P hPA hP).carriedComponent h00 hc hκ hs hv E)
    (X.selectedPiece_bundle_subset P)
    (X.carriedComponent_restriction_point h00 hc hκ hs hv D P hPA hP E hPoint)

end DiamondIntegral.Section6
