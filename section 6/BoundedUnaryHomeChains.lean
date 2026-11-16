import «section 6».CarriedUnaryHomeChains

/-! Double bounds on every actual intermediate domain of a finite
relatively unary composition, including all carried disc coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {f : Map A B} {π : Fin r → Fin s}
namespace RetainedUnaryHomeChain

def DoublyBounded : {r s : ℕ} → {A : DefSet (rawMixedSpace (M := M) n r) S} →
    {B : DefSet (rawMixedSpace (M := M) n s) S} → {f : Map A B} → {π : Fin r → Fin s} →
    RetainedUnaryHomeChain (G := G) S f π → Prop
  | _,_,A,_,_,_,.identity _ _ => VFDoublyBounded A.carrier
  | _,_,A,B,_,_,.unary _ _ _ _ _ => VFDoublyBounded A.carrier ∧ VFDoublyBounded B.carrier
  | _,_,_,_,_,_,.comp F H => F.DoublyBounded ∧ H.DoublyBounded

theorem DoublyBounded.source {F : RetainedUnaryHomeChain (G := G) S f π} (h : F.DoublyBounded) :
    VFDoublyBounded A.carrier := by
  induction F with
  | identity A hA => exact h
  | unary j hHome hRelative hUnit hRetain => exact h.1
  | comp first second ihf ihg => exact ihf h.1

theorem DoublyBounded.target {F : RetainedUnaryHomeChain (G := G) S f π} (h : F.DoublyBounded) :
    VFDoublyBounded B.carrier := by
  induction F with
  | identity A hA => exact h
  | unary j hHome hRelative hUnit hRetain => exact h.2
  | comp first second ihf ihg => exact ihg h.2

theorem doublyBounded_changeMap {g : Map A B} (F : RetainedUnaryHomeChain (G := G) S f π) (he : f=g) :
    (F.changeMap he).DoublyBounded ↔ F.DoublyBounded := by
  cases he
  rfl

theorem doublyBounded_carryLast
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : RetainedUnaryHomeChain (G := G) S f π) (k : Fin r) (h : F.DoublyBounded) :
    (F.carryLast h00 hc linear hκ hs hv hsmall hΓ k).DoublyBounded := by
  induction F with
  | identity A hA =>
    apply (doublyBounded_changeMap _ _).mpr
    exact rvCoordinateBundle_doublyBounded A k h hA.rvBounded
  | @unary r s A B f π j hHome hRelative hUnit hRetain =>
    exact ⟨rvCoordinateBundle_doublyBounded A k h.1
      (hHome.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ).rvBounded,
      rvCoordinateBundle_doublyBounded B (π k) h.2
      (hHome.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hHome.bijective.surjective).rvBounded⟩
  | @comp r s t A B C f g π σ first second ihf ihg =>
    apply (doublyBounded_changeMap _ _).mpr
    exact ⟨ihf k h.1,ihg (π k) h.2⟩

end RetainedUnaryHomeChain
end DiamondIntegral.Section6
