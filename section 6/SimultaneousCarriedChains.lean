import «section 6».SimultaneousPrimitiveLifts

/-! The complete carried finite-chain transport with one common
ambient map, literal special restrictions on every protected piece,
and exact preparation of every carried image. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M} {I : Type*}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem SimultaneousCentripetalChain.carried_lift_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SimultaneousCentripetalChain (G := G) I A B f P) :
    ∀ X : CarriedRefinementFrame A, Nonempty (SimultaneousCarriedLift (G := G) X f P) := by
  induction h with
  | identity A hA P hPA hP =>
    intro X
    exact ⟨SimultaneousCarriedLift.identity h00 hc hκ hs hv X P hP⟩
  | regularize A hA hVF P hPA hP hPVF =>
    intro X
    exact ⟨SimultaneousCarriedLift.regularize h00 hc hκ hs hv X P hP⟩
  | centripetal A D P hPA E hPoint =>
    intro X
    exact ⟨SimultaneousCarriedLift.centripetal h00 hc hκ hs hv X D P hPA E hPoint⟩
  | comp P hPA hf hg ihf ihg =>
    intro X
    obtain ⟨F⟩ := ihf X
    obtain ⟨H⟩ := ihg F.lift.target
    exact ⟨SimultaneousCarriedLift.comp h00 hPA (hf.toChain.toSpecial.bijective h00).injective F H⟩

theorem SimultaneousCentripetalChain.carried_preparation_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {P : I → DefSet (rawMixedSpace (M := M) n r) S}
    (h : SimultaneousCentripetalChain (G := G) I A B f P)
    (hPA : ∀ i, (P i).carrier ⊆ A.carrier)
    (hPrepared : ∀ i, IsRVPullback (f.restrict (hPA i)).image.carrier)
    (X : CarriedRefinementFrame A) :
    ∃ F : SimultaneousCarriedLift (G := G) X f P,
      ∀ i, IsRVPullback (F.lift.map.restrict (X.selectedPiece_bundle_subset (P i))).image.carrier := by
  obtain ⟨F⟩ := h.carried_lift_exists h00 hc hκ hs hv X
  refine ⟨F,fun i => ?_⟩
  exact F.lift.partition_image_pullback h00 (h.toChain.toSpecial.bijective h00).injective
    (P i) (hPA i) (hPrepared i)

end DiamondIntegral.Section6
