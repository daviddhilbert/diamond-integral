import «section 6».BinaryDisplacementPreparation
import «section 6».OrderedContractionLiftProperties

/-! Actual binary standard contractions in last-coordinate-first order
for every doubly bounded proper source. Its first coordinate is restored
during the first stage, then contracted by the complete unary theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_binary_contraction_stage
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier) : Nonempty (StandardContractionStage (G := G) A) := by
  obtain ⟨s,B,f,H,hB,hBD,hBRP,hDisp,k,hLeading⟩ := binary_displacement_preparation
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA hAD
  apply contraction_stage_of_rv_displacements h00 hc linear hκ hs hv hsmall hΓ H hAD hBD hBRP k hLeading
  intro i
  fin_cases i
  exact hDisp

theorem ordered_standard_program_binary_doublyBounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier) :
    ∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      Nonempty (OrderedStandardContractionProgram (G := G) S A U) := by
  obtain ⟨T⟩ := exists_binary_contraction_stage h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA hAD
  obtain ⟨q,U,⟨tail⟩⟩ := ordered_standard_program_unary h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    T.contracted T.contracted_proper
  exact ⟨q,U,⟨.step T tail⟩⟩

theorem lemma_6_27_binary_doublyBounded
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier) :
    ∃ q,∃ U : DefSet (rawMixedSpace (M := M) 0 q) S,
      ∃ T : OrderedStandardContractionProgram (G := G) S A U,Nonempty (OrderedStandardContractionLift T) := by
  obtain ⟨q,U,⟨T⟩⟩ := ordered_standard_program_binary_doublyBounded
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA hAD
  exact ⟨q,U,T,exists_ordered_standard_contraction_lift h00 hc linear hκ hs hv hsmall hΓ T hA⟩

end DiamondIntegral.Section6
