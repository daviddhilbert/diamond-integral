import «section 4».RVT001MeasuredDescent
import «section 4».RVT001OrdinaryDescent
import «section 4».RESPointNonvanishing

/-! The two numbered retraction statements, with all clauses assembled,
relative to the explicit approved upstream presentation transport.
Point nonvanishing and distinctness are proved, not additional inputs.
No unrestricted T001 presentation is inferred by these statements. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVT001RetractionStatements
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)
include hc h00 linear hκ hs hr hγ hΓ

theorem measured_evaluations_distinct (p : ApprovedT001Presentation.Measured B) :
    RVT001MeasuredDescent.evaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.geometric ≠
      RVT001MeasuredDescent.evaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.bounded :=
  RVT001MeasuredDescent.distinct_of_point_ne_zero h00 linear hκ hs B hr hγ hΓ p
    (RESPointNonvanishing.point_ne_zero_acvf00 hc h00 B)

theorem proposition_4_7 (p : ApprovedT001Presentation.Measured B) :
    ∃ E_g E_b : GradedRingHom (RVGrading.gradedPiece B) (RESReductionGradings.measuredPiece B),
      E_g ≠ E_b ∧
      E_g (RVMeasuredSpecialClasses.pClass B) = 0 ∧
      E_b (RVMeasuredSpecialClasses.pClass B) = 0 ∧
      (∀ x : RESChartRing.Ring B,
        E_g (RVChartMaps.ofRES B x) = RESMeasuredReduction.quotient B x ∧
        E_b (RVChartMaps.ofRES B x) = RESMeasuredReduction.quotient B x) ∧
      E_g (RVMeasuredSpecialClasses.hClass B) = RESMeasuredReduction.pointClass B ∧
      E_b (RVMeasuredSpecialClasses.hClass B) = 0 := by
  refine ⟨RVT001MeasuredDescent.gradedEvaluation h00 linear hκ hs B hr hγ hΓ p .geometric,
    RVT001MeasuredDescent.gradedEvaluation h00 linear hκ hs B hr hγ hΓ p .bounded,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro he
    exact measured_evaluations_distinct hc h00 linear hκ hs B hr hγ hΓ p
      (congrArg GradedRingHom.toRingHom he)
  · exact RVT001MeasuredDescent.evaluation_p h00 linear hκ hs B hr hγ hΓ p .geometric
  · exact RVT001MeasuredDescent.evaluation_p h00 linear hκ hs B hr hγ hΓ p .bounded
  · intro x
    exact ⟨RVT001MeasuredDescent.evaluation_res h00 linear hκ hs B hr hγ hΓ p .geometric x,
      RVT001MeasuredDescent.evaluation_res h00 linear hκ hs B hr hγ hΓ p .bounded x⟩
  · exact RVT001MeasuredDescent.evaluation_h_geometric h00 linear hκ hs B hr hγ hΓ p
  · exact RVT001MeasuredDescent.evaluation_h_bounded h00 linear hκ hs B hr hγ hΓ p

omit hc in
theorem proposition_4_15 (p : ApprovedT001Presentation.Ordinary B) :
    ∃ E : GradedRingHom (RVBoundedGrading.gradedPiece B) (RESReductionGradings.ordinaryPiece B),
      RVRadiusIdeal.radiusIdeal B ≤ RingHom.ker E.toRingHom ∧
      ∀ x : RESChartRing.Ring B,
        E (RVBoundedMaps.ofRES B x) = RESOrdinaryReduction.forget B x := by
  refine ⟨RVT001OrdinaryDescent.gradedBoundedEvaluation h00 linear hκ hs B hr hγ hΓ p .bounded,
    ?_, ?_⟩
  · exact RVT001OrdinaryDescent.radiusIdeal_le_kernel h00 linear hκ hs B hr hγ hΓ p .bounded
  · exact RVT001OrdinaryDescent.boundedEvaluation_res h00 linear hκ hs B hr hγ hΓ p .bounded

end DiamondIntegral.Section4.RVT001RetractionStatements
