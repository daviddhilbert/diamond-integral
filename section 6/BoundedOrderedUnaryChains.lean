import «section 6».BoundedUnaryHomeChains
import «section 6».OrderedLiftUnaryChains
import «section 6».HeadStartUnaryChains
import «section 6».OrderedContractionHeadStarts

/-! Full ordered lifts and all their head starts have actual finite
relatively unary compositions with every intermediate double bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

namespace RetainedUnaryHomeChain
variable {s : ℕ} {A : DefSet (rawMixedSpace (M := M) n r) S}
variable {B C : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {σ : Fin r → Fin s}

def changeTarget (F : RetainedUnaryHomeChain (G := G) S f σ) (he : B=C) :
    RetainedUnaryHomeChain (G := G) S (changeMapTarget f he) σ := by
  cases he
  exact F

theorem doublyBounded_changeTarget (F : RetainedUnaryHomeChain (G := G) S f σ) (he : B=C) :
    (F.changeTarget he).DoublyBounded ↔ F.DoublyBounded := by
  cases he
  rfl

theorem doublyBounded_carryHeadStart
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (F : RetainedUnaryHomeChain (G := G) S f σ) (h : F.DoublyBounded)
    (k : ℕ) (π : Fin k → Fin r) :
    (F.carryHeadStart h00 hc linear hκ hs hv hsmall hΓ k π).DoublyBounded := by
  induction k with
  | zero => exact h
  | succ k ih =>
    exact doublyBounded_carryLast h00 hc linear hκ hs hv hsmall hΓ _ _ (ih (π ∘ Fin.castSucc))

end RetainedUnaryHomeChain

variable {A : DefSet (rawMixedSpace (M := M) n r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
variable {T : OrderedStandardContractionProgram (G := G) S A U}
variable {B : DefSet (rawMixedSpace (M := M) n q) S} {f : Map A B}

theorem IsOrderedProgramLift.bounded_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (h : IsOrderedProgramLift S T f) : ProperInvariant S A.carrier → VFDoublyBounded A.carrier →
    ∃ F : RetainedUnaryHomeChain (G := G) S f T.oldLabels,F.DoublyBounded := by
  induction h with
  | zero A =>
    intro hA hAD
    exact ⟨.identity A hA,hAD⟩
  | @step n r q A U R tail B f hTail hLabels hTarget ih =>
    intro hA hAD
    obtain ⟨F,hF⟩ := ih R.contracted_proper R.contracted_doublyBounded
    let H := F.carryLast h00 hc linear hκ hs hv hsmall hΓ R.leading
    let L : RetainedUnaryHomeChain (G := G) S (changeMapTarget R.lift hTarget) R.oldLabels :=
      .unary (Fin.last n) (R.home.changeMapTarget hTarget)
        (by
          intro p i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · intro hNe
            exact (hNe rfl).elim
          · intro _
            rw [changeMapTarget_value]
            exact R.relative p j)
        (fun p hInd => (R.unitDerivative p
          (not_mem_small_set_of_independent hc R.exceptional R.exceptional_dim p.val hInd)).changeMapTarget hTarget)
        (by intro p i; rw [changeMapTarget_value]; exact R.retained p i)
    refine ⟨.comp L H,⟨?_,?_⟩⟩
    · exact ⟨hAD,hTarget ▸ R.doublyBounded⟩
    · exact F.doublyBounded_carryLast h00 hc linear hκ hs hv hsmall hΓ R.leading hF

theorem OrderedStandardContractionLift.bounded_relatively_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (V : OrderedStandardContractionLift T) (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier) :
    ∃ F : RetainedUnaryHomeChain (G := G) S V.map T.oldLabels,F.DoublyBounded :=
  V.ordered.bounded_unary_chain h00 hc linear hκ hs hv hsmall hΓ hA hAD

theorem OrderedStandardContractionLift.headStartLift_bounded_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (V : OrderedStandardContractionLift T) (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (k : ℕ) (π : Fin k → Fin r) :
    ∃ F : RetainedUnaryHomeChain (G := G) S (V.headStartLift k π) T.oldLabels,F.DoublyBounded := by
  obtain ⟨F,hF⟩ := V.bounded_relatively_unary_chain h00 hc linear hκ hs hv hsmall hΓ hA hAD
  let H := F.carryHeadStart h00 hc linear hκ hs hv hsmall hΓ k π
  refine ⟨H.changeTarget (V.headStart_target_eq k π),?_⟩
  apply (H.doublyBounded_changeTarget _).mpr
  exact F.doublyBounded_carryHeadStart h00 hc linear hκ hs hv hsmall hΓ hF k π

end DiamondIntegral.Section6
