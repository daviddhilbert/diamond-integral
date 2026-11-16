import «section 6».CarriedUnaryHomeChains
import «section 6».OrderedStandardContractionLifts

/-! The actual full lift of an ordered standard contraction is a finite
composition of relatively unary proper covariant homeomorphisms. This
uses the recorded stage composition, rather than only the properties of
its resulting map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}
variable {T : OrderedStandardContractionProgram (G := G) S A U}
variable {B : DefSet (rawMixedSpace (M := M) n q) S} {f : Map A B}

theorem IsOrderedProgramLift.unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (h : IsOrderedProgramLift S T f) : ProperInvariant S A.carrier →
    Nonempty (RetainedUnaryHomeChain (G := G) S f T.oldLabels) := by
  induction h with
  | zero A =>
    intro hA
    exact ⟨.identity A hA⟩
  | @step n r q A U R tail B f hTail hLabels hTarget ih =>
    intro hA
    obtain ⟨F⟩ := ih R.contracted_proper
    let H := F.carryLast h00 hc linear hκ hs hv hsmall hΓ R.leading
    have hStage : RetainedUnaryHomeChain (G := G) S (changeMapTarget R.lift hTarget) R.oldLabels := by
      refine .unary (Fin.last n) (R.home.changeMapTarget hTarget) ?_ ?_ ?_
      · intro p i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · intro hNe
          exact (hNe rfl).elim
        · intro _
          rw [changeMapTarget_value]
          exact R.relative p j
      · intro p hInd
        exact (R.unitDerivative p
          (not_mem_small_set_of_independent hc R.exceptional R.exceptional_dim p.val hInd)).changeMapTarget hTarget
      · intro p i
        rw [changeMapTarget_value]
        exact R.retained p i
    exact ⟨.comp hStage H⟩

theorem OrderedStandardContractionLift.relatively_unary_chain
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (V : OrderedStandardContractionLift T) (hA : ProperInvariant S A.carrier) :
    Nonempty (RetainedUnaryHomeChain (G := G) S V.map T.oldLabels) :=
  V.ordered.unary_chain h00 hc linear hκ hs hv hsmall hΓ hA

end DiamondIntegral.Section6
