import «section 6».BinaryMeasuredDisplacementPreparation
import «section 6».RegularizedMeasuredPreparations
import «section 6».MeasuredOrderedProgramData

/-! Actual binary measured ordered programs. The full prepared Gamma
form is recovered from the retained preparation labels after the base
has been restored and contracted last. -/

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

theorem binary_measured_ordered_program
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hV : ∀ a ∈ V,iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V,x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A : DefSet (rawMixedSpace (M := M) 2 r) S) (hA : ProperInvariant S A.carrier)
    (hAD : VFDoublyBounded A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {a : Fin 2 → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    Nonempty (MeasuredOrderedProgram (G := G) A ω) := by
  obtain ⟨T,hDisp⟩ := binary_measured_displacement_preparation
    h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt A hA hAD ω hLevels
  let R := T.regularizeAmbient h00 hc hκ hs hv
  have hRD := T.regularizeAmbient_displacement h00 hc hκ hs hv 0 hDisp
  obtain ⟨k,hLeading⟩ := T.regularizeAmbient_leading h00 hc hκ hs hv
  let hf := R.special.bijective h00
  have hAll : ∀ i : Fin 1,RVCoordinateDisplacement R.map i.castSucc := by
    intro i
    fin_cases i
    exact hRD
  obtain ⟨D⟩ := restored_complement_stage_label_data h00 hc linear hκ hs hv hsmall hΓ R.special hAD
    R.doublyBounded R.prepared k hLeading (complementUndoShift R.map hf)
    (complementUndoShift_rv_constant R.map hf hAll) (complementUndoShift_last R.map hf)
    (complementUndoShift_restores R.map hf)
  obtain ⟨q,U,⟨tail⟩⟩ := ordered_standard_program_unary h00 hc linear hκ hs hv V hsmall hΓ hV hVS hSV hnt
    D.stage.contracted D.stage.contracted_proper
  exact ⟨MeasuredOrderedProgram.of_restored_preparation R D tail⟩

end DiamondIntegral.Section6
