import «section 6».NormalizedOrderedUnaryChains
import «section 6».NormalizedMeasuredHeadStartLifts

/-! The original-source measured head-start lift is a finite
composition of actual relatively unary proper homeomorphisms. When the
original source is doubly bounded, all its intermediate domains are too. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)} {e : Equiv.Perm (Fin (n+1))}
namespace NormalizedMeasuredContraction

theorem relatively_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : NormalizedMeasuredContraction (G := G) A ω e) :
    ∃ H : RetainedUnaryHomeChain (G := G) S F.map F.oldIndex,VFDoublyBounded A.carrier → H.DoublyBounded :=
  F.normalization.normalizedOrderedMap_unary_chain h00 hc linear hκ hs hv hsmall hΓ (Nat.zero_lt_succ n) F.preparedContraction.lift

theorem headStartLift_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : NormalizedMeasuredContraction (G := G) A ω e) (k : ℕ) (π : Fin k → Fin r) :
    ∃ H : RetainedUnaryHomeChain (G := G) S (F.headStartLift h00 hc linear hκ hs hv hsmall hΓ k π) F.oldIndex,
      VFDoublyBounded A.carrier → H.DoublyBounded := by
  obtain ⟨H,hH⟩ := F.relatively_unary_chain h00 hc linear hκ hs hv hsmall hΓ
  let K := H.carryHeadStart h00 hc linear hκ hs hv hsmall hΓ k π
  refine ⟨K.changeTarget (F.headStart_target_eq k π),fun hAD => ?_⟩
  apply (K.doublyBounded_changeTarget _).mpr
  exact H.doublyBounded_carryHeadStart h00 hc linear hκ hs hv hsmall hΓ (hH hAD) k π

end NormalizedMeasuredContraction
end DiamondIntegral.Section6
