import «section 6».StandardContractionStages

/-! Finite ordered contraction programs store an actual relatively unary
stage before dropping each VF coordinate. Their contracted maps retain
all original labels and proper bounds. Prepared RV-pullbacks have actual
programs in every dimension, including the empty VF tuple. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

inductive OrderedStandardContractionProgram (S : Set M) :
    {n r q : ℕ} → DefSet (rawMixedSpace (M := M) n r) S → DefSet (rawMixedSpace (M := M) 0 q) S → Type where
  | zero {r : ℕ} (A : DefSet (rawMixedSpace (M := M) 0 r) S) : OrderedStandardContractionProgram S A A
  | step {n r q : ℕ} {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
      {U : DefSet (rawMixedSpace (M := M) 0 q) S}
      (T : StandardContractionStage (G := G) A) (tail : OrderedStandardContractionProgram S T.contracted U) :
      OrderedStandardContractionProgram S A U

namespace OrderedStandardContractionProgram
variable {S : Set M} {n r q : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {U : DefSet (rawMixedSpace (M := M) 0 q) S}

def toMap (T : OrderedStandardContractionProgram (G := G) S A U) : Map A U := by
  induction T with
  | zero A => exact Map.id A
  | step T tail ih => exact ih.comp T.contraction

theorem surjective (T : OrderedStandardContractionProgram (G := G) S A U) : Function.Surjective T.toMap := by
  induction T with
  | zero A => exact Function.surjective_id
  | step T tail ih => exact ih.comp T.contraction_surjective

def oldLabels (T : OrderedStandardContractionProgram (G := G) S A U) : Fin r → Fin q := by
  induction T with
  | zero A => exact id
  | step T tail ih => exact ih ∘ T.oldLabels

theorem oldLabels_injective (T : OrderedStandardContractionProgram (G := G) S A U) : Function.Injective T.oldLabels := by
  induction T with
  | zero A => exact Function.injective_id
  | step T tail ih => exact ih.comp T.oldLabels_injective

theorem retained (T : OrderedStandardContractionProgram (G := G) S A U) (p : A) (i : Fin r) :
    (T.toMap p).val.2 (T.oldLabels i)=p.val.2 i := by
  induction T with
  | zero A => rfl
  | step T tail ih =>
    exact (ih (T.contraction p) (T.oldLabels i)).trans (T.contraction_retains_old_labels p i)

def volumeIndex (T : OrderedStandardContractionProgram (G := G) S A U) : Fin n → Fin q := by
  induction T with
  | zero A => exact Fin.elim0
  | step T tail ih => exact Fin.lastCases (tail.oldLabels T.leading) ih

theorem volumeIndex_step_last
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (T : StandardContractionStage (G := G) A)
    (tail : OrderedStandardContractionProgram (G := G) S T.contracted U) :
    (step T tail).volumeIndex (Fin.last n)=tail.oldLabels T.leading := by
  simp only [volumeIndex,Fin.lastCases_last]

theorem volumeIndex_step_castSucc
    {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
    (T : StandardContractionStage (G := G) A)
    (tail : OrderedStandardContractionProgram (G := G) S T.contracted U) (i : Fin n) :
    (step T tail).volumeIndex i.castSucc=tail.volumeIndex i := by
  simp only [volumeIndex,Fin.lastCases_castSucc]

theorem target_proper (T : OrderedStandardContractionProgram (G := G) S A U)
    (hA : ProperInvariant S A.carrier) : ProperInvariant S U.carrier := by
  induction T with
  | zero A => exact hA
  | step T tail ih => exact ih T.contracted_proper

theorem target_rvBounded (T : OrderedStandardContractionProgram (G := G) S A U)
    (hA : ProperInvariant S A.carrier) : RVSupportDoublyBounded U.carrier := (T.target_proper hA).rvBounded

end OrderedStandardContractionProgram

theorem ordered_standard_program_of_doublyBounded_pullback
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (S : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (n : ℕ) : ∀ r,(A : DefSet (rawMixedSpace (M := M) n r) S) →
      ProperInvariant S A.carrier → VFDoublyBounded A.carrier → IsRVPullback A.carrier →
      ∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
        Nonempty (OrderedStandardContractionProgram (G := G) S A U) := by
  induction n with
  | zero =>
    intro r A hA hD hRP
    exact ⟨r,A,⟨.zero A⟩⟩
  | succ n ih =>
    intro r A hA hD hRP
    obtain ⟨T,hTRP⟩ := exists_regularization_contraction_stage h00 hc linear hκ hs hv hsmall hΓ A hA hD hRP
    obtain ⟨q,U,⟨tail⟩⟩ := ih T.arity T.contracted T.contracted_proper T.contracted_doublyBounded
      (vfDropLast_image_rvPullback hTRP)
    exact ⟨q,U,⟨.step T tail⟩⟩

end DiamondIntegral.Section6
