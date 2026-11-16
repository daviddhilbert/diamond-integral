import «section 6».RVRefinementGammaForms

/-! A whole form-compatible chain lifts through an actual refinement
of RV labels. Composition retains the full intermediate Gamma map and
uses the exact protected images given by the commuting square. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem FormCompatibleSynchronizedChain.rv_refinement_lift_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (h : FormCompatibleSynchronizedChain (G := G) I A B f P ω) :
    ∀ X : RVRefinementFrame A,∃ F : RVRefinementChainLift (G := G) X f P,
      FormCompatibleSynchronizedChain (G := G) I X.base F.target.base F.map
        (fun i => X.selectedPiece (P i)) (ω.comp X.oldMap) := by
  induction h with
  | identity A hA P hPA hP ω =>
    intro X
    refine ⟨RVRefinementChainLift.identity h00 hc hκ hs hv X P hP,?_⟩
    exact .identity X.base X.proper _ (fun i => X.selectedPiece_subset (P i))
      (fun i => X.selectedPiece_properInvariant h00 hc hκ hs hv (P i) (hP i)) (ω.comp X.oldMap)
  | regularize A hA hVF P hPA hP hPVF ω =>
    intro X
    refine ⟨RVRefinementChainLift.regularize h00 hc hκ hs hv X P hP,?_⟩
    exact .regularize X.base X.proper X.doublyBounded _ (fun i => X.selectedPiece_subset (P i))
      (fun i => X.selectedPiece_properInvariant h00 hc hκ hs hv (P i) (hP i))
      (fun i => X.selectedPiece_doublyBounded (P i)) (ω.comp X.oldMap)
  | centripetal A D P hPA E hData ω hSafe =>
    intro X
    refine ⟨RVRefinementChainLift.centripetal h00 hc hκ hs hv X D P hPA E hData,?_⟩
    exact .centripetal X.base (X.portComponent D) _ (fun i => X.selectedPiece_subset (P i))
      (fun i => (X.pieceFrame h00 hc hκ hs hv (P i) (hPA i) (E i).sourceProper).portComponent (E i))
      (fun i => X.portComponent_restriction_data h00 hc hκ hs hv D (E i) (hPA i) (hData i))
      (ω.comp X.oldMap) (X.portComponent_core_form_constant D ω hSafe)
  | comp P hPA hf η hTransport hg ihf ihg =>
    intro X
    obtain ⟨F,hF⟩ := ihf X
    obtain ⟨H,hH⟩ := ihg F.target
    have hinj := (hf.toSynchronized.toChain.toSpecial.bijective h00).injective
    refine ⟨F.comp h00 hinj hPA H,?_⟩
    exact .comp _ (fun i => X.selectedPiece_subset (P i)) hF (η.comp F.target.oldMap)
      (F.gamma_form_transport _ η hTransport)
      (hH.changePieces (fun i => (F.partition_image h00 hinj i (hPA i)).symm))

end DiamondIntegral.Section6
