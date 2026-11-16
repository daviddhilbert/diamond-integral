import «section 6».CarriedSynchronizedCertificates
import «section 6».SimultaneousCarriedChains

/-! An actual simultaneous centripetal chain has a carried lift that
retains its common permitted component certificate. This certificate
can be carried again in the next preparation dimension. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem SynchronizedCentripetalChain.carried_synchronized_lift_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SynchronizedCentripetalChain (G := G) I A B f P) :
    ∀ X : CarriedRefinementFrame A,∃ F : SimultaneousCarriedLift (G := G) X f P,
      SynchronizedCentripetalChain (G := G) I X.bundle F.lift.target.bundle F.lift.map
        (fun i => rvCoordinateBundle (X.selectedPiece (P i)) X.freeLabel) := by
  induction h with
  | identity A hA P hPA hP =>
    intro X
    exact ⟨SimultaneousCarriedLift.identity h00 hc hκ hs hv X P hP,
      SimultaneousCarriedLift.identity_synchronized_certificate h00 hc hκ hs hv X P hP⟩
  | regularize A hA hVF P hPA hP hPVF =>
    intro X
    exact ⟨SimultaneousCarriedLift.regularize h00 hc hκ hs hv X P hP,
      SimultaneousCarriedLift.regularize_synchronized_certificate h00 hc hκ hs hv X P hP⟩
  | centripetal A D P hPA E hData =>
    intro X
    exact ⟨SimultaneousCarriedLift.centripetal h00 hc hκ hs hv X D P hPA E (fun i p hp => (hData i).point p hp),
      SimultaneousCarriedLift.centripetal_synchronized_certificate h00 hc hκ hs hv X D P hPA E hData⟩
  | comp P hPA hf hg ihf ihg =>
    intro X
    obtain ⟨F,hF⟩ := ihf X
    obtain ⟨H,hH⟩ := ihg F.lift.target
    have hinj := (hf.toChain.toSpecial.bijective h00).injective
    let K := SimultaneousCarriedLift.comp h00 hPA hinj F H
    refine ⟨K,SynchronizedCentripetalChain.comp _ (fun i => X.selectedPiece_bundle_subset (P i)) hF ?_⟩
    exact hH.changePieces (fun i => defSet_eq_of_carrier_eq
      (F.lift.partition_image h00 hinj (P i) (hPA i)).symm)

end DiamondIntegral.Section6
