import «section 6».CarriedPrimitiveLifts

/-! Whole finite-chain transport for the lower-dimensional release
construction, after preliminary zero-centered preparation. Every lift
is a literal special covariant chain, keeps the carried VF coordinate,
and retains the exact old-coordinate and RV-label commutation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r s : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalChain.carried_lift_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} (h : CentripetalChain (G := G) A B f) :
    ∀ X : CarriedRefinementFrame A, Nonempty (CarriedChainLift (G := G) X f) := by
  induction h with
  | identity A hA =>
    intro X
    exact ⟨CarriedChainLift.identity h00 hc hκ hs hv X⟩
  | regularize A hA hVF =>
    intro X
    exact ⟨CarriedChainLift.regularize h00 hc hκ hs hv X⟩
  | centripetal A D =>
    intro X
    exact ⟨CarriedChainLift.centripetal h00 hc hκ hs hv X D⟩
  | comp hf hg ihf ihg =>
    intro X
    obtain ⟨F⟩ := ihf X
    obtain ⟨H⟩ := ihg F.target
    exact ⟨F.comp H⟩

theorem CarriedChainLift.target_pullback
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} {X : CarriedRefinementFrame A} (F : CarriedChainLift (G := G) X f)
    (hB : IsRVPullback B.carrier) : IsRVPullback F.target.bundle.carrier :=
  F.target.pullback hB

theorem CentripetalChain.carried_preparation_exists
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    {f : Map A B} (h : CentripetalChain (G := G) A B f) (hB : IsRVPullback B.carrier)
    (k : Fin r) (hA : ProperInvariant S A.carrier) (hDouble : VFDoublyBounded A.carrier) :
    ∃ F : CarriedChainLift (G := G) (CarriedRefinementFrame.identity A k hA hDouble) f,
      IsRVPullback F.target.bundle.carrier := by
  obtain ⟨F⟩ := h.carried_lift_exists h00 hc hκ hs hv (CarriedRefinementFrame.identity A k hA hDouble)
  exact ⟨F,F.target_pullback hB⟩

end DiamondIntegral.Section6
