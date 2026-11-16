import «section 6».VFConjugatedMaps
import «section 6».BoundedUnaryHomeChains

/-! Every step of an actual finite relatively unary chain may be
conjugated by a fixed VF coordinate relabeling. Intermediate double
bounds and all retained-label selectors are preserved. -/

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

def reindex
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : RetainedUnaryHomeChain (G := G) S f π) (e : Equiv.Perm (Fin n)) :
    RetainedUnaryHomeChain (G := G) S (reindexVFConjugate f e) π := by
  induction F with
  | identity A hA =>
    exact (RetainedUnaryHomeChain.identity (reindexedVFSet A e) (reindexedVFSet_properInvariant A e hA)).changeMap
      (reindexVFConjugate_identity A e).symm
  | @unary r s A B f π j hHome hRelative hUnit hRetain =>
    have hA := hHome.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
    have hB := hHome.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hHome.bijective.surjective
    exact .unary (e.symm j) (reindexVFConjugate_homeomorphism h00 hc linear hκ hs hv hsmall hΓ f e hHome)
      (reindexVFConjugate_relative f e j hRelative)
      (reindexVFConjugate_generic_unit hv f e hA hB hUnit)
      (reindexVFConjugate_retained f e π hRetain)
  | @comp r s t A B C f g π σ first second ihf ihg =>
    exact (RetainedUnaryHomeChain.comp ihf ihg).changeMap (reindexVFConjugate_comp f g e).symm

theorem doublyBounded_reindex
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : RetainedUnaryHomeChain (G := G) S f π) (e : Equiv.Perm (Fin n)) (h : F.DoublyBounded) :
    (F.reindex h00 hc linear hκ hs hv hsmall hΓ e).DoublyBounded := by
  induction F with
  | identity A hA =>
    apply (doublyBounded_changeMap _ _).mpr
    exact reindexedVFSet_doublyBounded A e h
  | @unary r s A B f π j hHome hRelative hUnit hRetain =>
    exact ⟨reindexedVFSet_doublyBounded A e h.1,reindexedVFSet_doublyBounded B e h.2⟩
  | comp first second ihf ihg =>
    apply (doublyBounded_changeMap _ _).mpr
    exact ⟨ihf h.1,ihg h.2⟩

end RetainedUnaryHomeChain
end DiamondIntegral.Section6
