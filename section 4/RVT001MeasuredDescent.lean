import «section 4».ApprovedT001Presentation
import «section 4».CoactionSurjectiveDescent
import «section 4».RVBalancedSpecialClasses
import «section 4».RVBalancedMapGradings

/-! Measured RV Euler maps descended using the author-approved T001
coefficient-kernel presentation as an explicit transported hypothesis.
They preserve the actual grading, restrict to the measured RES quotient,
kill P, and have the stated values on h. Distinctness still requires
nonvanishing of the degree-one point class. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVT001MeasuredDescent
open PolynomialCoactionGrading.Coaction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (p : ApprovedT001Presentation.Measured B)

include p in
theorem kernel_le (kind : EulerKind) :
    RingHom.ker (RVFiniteBalancedTensor.comparison B).toRingHom ≤
      RingHom.ker (RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ kind).toRingHom :=
  p.kernel_le.trans
    (RVCoefficientCoordinateTranslationKernel.coefficientIdeal_le_evaluation_ker h00 linear hκ hs B hr hγ hΓ kind)

def evaluation (kind : EulerKind) : RVChartRing.Ring B →+* RESMeasuredReduction.ReducedRing B :=
  surjectiveDescent (RVFiniteBalancedTensor.comparison B).toRingHom p.surjective
    (RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ kind).toRingHom
    (kernel_le h00 linear hκ hs B hr hγ hΓ p kind)

theorem evaluation_comparison (kind : EulerKind) (x : RVFiniteBalancedTensor.Source B) :
    evaluation h00 linear hκ hs B hr hγ hΓ p kind (RVFiniteBalancedTensor.comparison B x) =
      RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ kind x :=
  surjectiveDescent_apply _ _ _ _ x

def gradedEvaluation (kind : EulerKind) :
    GradedRingHom (RVGrading.gradedPiece B) (RESReductionGradings.measuredPiece B) :=
  gradedSurjectiveDescent (RVBalancedGradings.measuredCoaction B)
    (RVGrading.gradingCoaction B) (RESReductionGradings.measuredCoaction B)
    (RVFiniteBalancedTensor.comparison B).toRingHom p.surjective
    (fun _ _ hx => (RVBalancedMapGradings.gradedMeasuredComparison B).map_mem hx)
    (RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ kind).toRingHom
    (kernel_le h00 linear hκ hs B hr hγ hΓ p kind)
    (fun _ _ hx => (RVBalancedMapGradings.gradedMeasuredEvaluation h00 linear hκ hs B hr hγ hΓ kind).map_mem hx)

theorem evaluation_res (kind : EulerKind) (x : RESChartRing.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ p kind (RVChartMaps.ofRES B x) =
      RESMeasuredReduction.quotient B x := by
  rw [← RVFiniteBalancedTensor.comparison_res, evaluation_comparison, RVFiniteBalancedTensor.evaluation_res]

theorem evaluation_p (kind : EulerKind) :
    evaluation h00 linear hκ hs B hr hγ hΓ p kind (RVMeasuredSpecialClasses.pClass B) = 0 := by
  rw [← RVBalancedSpecialClasses.comparison_pPreimage, evaluation_comparison]
  exact RVBalancedSpecialClasses.evaluation_pPreimage h00 linear hκ hs B hr hγ hΓ kind

theorem evaluation_h_geometric :
    evaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.geometric (RVMeasuredSpecialClasses.hClass B) =
      RESMeasuredReduction.pointClass B := by
  rw [← RVBalancedSpecialClasses.comparison_hPreimage, evaluation_comparison]
  exact RVBalancedSpecialClasses.evaluation_hPreimage_geometric h00 linear hκ hs B hr hγ hΓ

theorem evaluation_h_bounded :
    evaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.bounded (RVMeasuredSpecialClasses.hClass B) = 0 := by
  rw [← RVBalancedSpecialClasses.comparison_hPreimage, evaluation_comparison]
  exact RVBalancedSpecialClasses.evaluation_hPreimage_bounded h00 linear hκ hs B hr hγ hΓ

theorem distinct_of_point_ne_zero (hQ : RESMeasuredReduction.pointClass B ≠ 0) :
    evaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.geometric ≠
      evaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.bounded := by
  intro heq
  have he := RingHom.congr_fun heq (RVMeasuredSpecialClasses.hClass B)
  rw [evaluation_h_geometric, evaluation_h_bounded] at he
  exact hQ he

end DiamondIntegral.Section4.RVT001MeasuredDescent
