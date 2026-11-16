import «section 6».CarriedComponentRestrictions
import «section 6».ApertureRestrictionData

/-! Carrying a component preserves its focus and coefficient on the
actual protected piece, as well as its point map. These identities
retain the full aperture restriction certificate in higher dimension. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CarriedRefinementFrame.carriedComponent_focus
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (D : CentripetalData (G := G) A) (p : Mixed M (n+1) X.arity) (hp : p ∈ X.bundle.carrier) :
    (X.carriedComponent h00 hc hκ hs hv D).extendedFocus p=
      D.extendedFocus (Fin.init p.1,p.2 ∘ X.labels) := by
  rw [CarriedRefinementFrame.carriedComponent,CentripetalData.carryCoordinate_extendedFocus _ _ _ _ hp]
  exact D.refineLabels_extendedFocus X.labels X.proper X.doublyBounded
    (labelRefinement_tagged A X.base X.labels X.fibres D.tagged) X.fibres (Fin.init p.1,p.2) hp.1

theorem CarriedRefinementFrame.carriedComponent_restriction_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A P : DefSet (rawMixedSpace (M := M) n r) S} (X : CarriedRefinementFrame A)
    (D : CentripetalData (G := G) A) (E : CentripetalData (G := G) P)
    (hPA : P.carrier ⊆ A.carrier) (hData : ApertureRestrictionData D E) :
    ApertureRestrictionData (X.carriedComponent h00 hc hκ hs hv D)
      ((X.pieceFrame h00 hc hκ hs hv P hPA E.sourceProper).carriedComponent h00 hc hκ hs hv E) := by
  refine ⟨X.selectedPiece_bundle_subset P,congrArg Fin.castSucc hData.coordinate,hData.coefficient,?_⟩
  intro p hp
  obtain ⟨hParent,hOld⟩ := (X.selectedPiece_bundle_mem P p).mp hp
  rw [(X.pieceFrame h00 hc hκ hs hv P hPA E.sourceProper).carriedComponent_focus h00 hc hκ hs hv E p hp,
    X.carriedComponent_focus h00 hc hκ hs hv D p hParent]
  exact hData.focus (Fin.init p.1,p.2 ∘ X.labels) hOld

end DiamondIntegral.Section6
