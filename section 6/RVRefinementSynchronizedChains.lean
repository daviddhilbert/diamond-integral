import «section 6».RVRefinementChainLifts
import «section 6».PreparedSynchronizedFamilies

/-! A synchronized preparation survives additional existing RV labels.
All lifted operations are literal permitted operations in the same VF
dimension, with the actual protected images used at composition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace RVRefinementFrame
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem portComponent_focus (X : RVRefinementFrame A) (D : CentripetalData (G := G) A)
    (p : Mixed M n X.arity) (hp : p ∈ X.base.carrier) :
    (X.portComponent D).extendedFocus p=D.extendedFocus (p.1,p.2 ∘ X.labels) :=
  D.refineLabels_extendedFocus X.labels X.proper X.doublyBounded
    (labelRefinement_tagged A X.base X.labels X.fibres D.tagged) X.fibres p hp

theorem portComponent_restriction_data
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : RVRefinementFrame A) (D : CentripetalData (G := G) A)
    {P : DefSet (rawMixedSpace (M := M) n r) S} (E : CentripetalData (G := G) P)
    (hPA : P.carrier ⊆ A.carrier) (hData : ApertureRestrictionData D E) :
    ApertureRestrictionData (X.portComponent D)
      ((X.pieceFrame h00 hc hκ hs hv P hPA E.sourceProper).portComponent E) := by
  refine ⟨X.selectedPiece_subset P,hData.coordinate,hData.coefficient,?_⟩
  intro p hp
  obtain ⟨hParent,hOld⟩ := (X.mem_selectedPiece P p).mp hp
  rw [(X.pieceFrame h00 hc hκ hs hv P hPA E.sourceProper).portComponent_focus E p hp,
    X.portComponent_focus D p hParent]
  exact hData.focus (p.1,p.2 ∘ X.labels) hOld

end RVRefinementFrame

def RVRefinementChainLift.centripetal
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} (X : RVRefinementFrame A)
    (D : CentripetalData (G := G) A) (P : I → DefSet (rawMixedSpace (M := M) n r) S)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier) (E : ∀ i,CentripetalData (G := G) (P i))
    (hData : ∀ i,ApertureRestrictionData D (E i)) :
    RVRefinementChainLift (G := G) X D.bijection P where
  target := X.afterCentripetal h00 hc hκ hs hv D
  map := (X.portComponent D).bijection
  chain := .centripetal X.base (X.portComponent D) _ (fun i => X.selectedPiece_subset (P i))
    (fun i => (X.pieceFrame h00 hc hκ hs hv (P i) (hPA i) (E i).sourceProper).portComponent (E i))
    (fun i => X.portComponent_restriction_data h00 hc hκ hs hv D (E i) (hPA i) (hData i))
  commutes p := D.refineLabels_point_commutes X.labels X.proper X.doublyBounded
    (labelRefinement_tagged A X.base X.labels X.fibres D.tagged) X.fibres p.val p.property

theorem SynchronizedCentripetalChain.rv_refinement_lift_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SynchronizedCentripetalChain (G := G) I A B f P) :
    ∀ X : RVRefinementFrame A,Nonempty (RVRefinementChainLift (G := G) X f P) := by
  induction h with
  | identity A hA P hPA hP =>
    intro X
    exact ⟨RVRefinementChainLift.identity h00 hc hκ hs hv X P hP⟩
  | regularize A hA hVF P hPA hP hPVF =>
    intro X
    exact ⟨RVRefinementChainLift.regularize h00 hc hκ hs hv X P hP⟩
  | centripetal A D P hPA E hData =>
    intro X
    exact ⟨RVRefinementChainLift.centripetal h00 hc hκ hs hv X D P hPA E hData⟩
  | comp P hPA hf hg ihf ihg =>
    intro X
    obtain ⟨F⟩ := ihf X
    obtain ⟨H⟩ := ihg F.target
    exact ⟨F.comp h00 (hf.toChain.toSpecial.bijective h00).injective hPA H⟩

theorem PreparedSynchronizedFamily.refine_rv_labels
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {P : I → DefSet (rawMixedSpace (M := M) n r) S} {hPA : ∀ i,(P i).carrier ⊆ A.carrier}
    (F : PreparedSynchronizedFamily (G := G) A P hPA) (X : RVRefinementFrame A) :
    Nonempty (PreparedSynchronizedFamily (G := G) X.base (fun i => X.selectedPiece (P i))
      (fun i => X.selectedPiece_subset (P i))) := by
  obtain ⟨K⟩ := F.chain.rv_refinement_lift_exists h00 hc hκ hs hv X
  refine ⟨⟨K.target.arity,K.target.base,K.map,K.chain,K.target.proper,K.target.doublyBounded,
    K.target.pullback F.pullback,fun i => ?_⟩⟩
  rw [K.partition_image h00 (F.chain.toChain.toSpecial.bijective h00).injective i (hPA i)]
  apply labelRefinement_pullback (F.map.restrict (hPA i)).image
    (K.target.selectedPiece (F.map.restrict (hPA i)).image) K.target.labels
    (K.target.selectedPiece_fibres _ ?_) (F.prepared i)
  rintro q ⟨p,hp⟩
  exact hp ▸ (F.map.restrict (hPA i) p).property

end DiamondIntegral.Section6
