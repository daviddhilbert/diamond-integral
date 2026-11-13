import «section 4».ApprovedT001Presentation
import «section 4».CoactionSurjectiveDescent
import «section 4».RVOrdinaryMapGradings

/-! Actual graded ordinary RV Euler maps relative to the transported
author-approved T001 presentation. Restricting along bounded measured RV
forgetfulness proves the bounded retraction and its radius vanishing
without any bounded tensor surjectivity or kernel premise. The T001
transport hypothesis is explicit throughout. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVT001OrdinaryDescent
open PolynomialCoactionGrading.Coaction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (p : ApprovedT001Presentation.Ordinary B)

include p in
theorem kernel_le (kind : EulerKind) :
    RingHom.ker (RVOrdinaryBalancedTensor.comparison B).toRingHom ≤
      RingHom.ker (RVOrdinaryBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ kind).toRingHom :=
  p.kernel_le.trans
    (RVOrdinaryCoefficientTranslationKernel.coefficientIdeal_le_evaluation_ker h00 linear hκ hs B hr hγ hΓ kind)

def evaluation (kind : EulerKind) : RVOrdinaryRing.Ring B →+* RESOrdinaryReduction.ReducedRing B :=
  surjectiveDescent (RVOrdinaryBalancedTensor.comparison B).toRingHom p.surjective
    (RVOrdinaryBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ kind).toRingHom
    (kernel_le h00 linear hκ hs B hr hγ hΓ p kind)

theorem evaluation_comparison (kind : EulerKind) (x : RVOrdinaryBalancedTensor.Source B) :
    evaluation h00 linear hκ hs B hr hγ hΓ p kind (RVOrdinaryBalancedTensor.comparison B x) =
      RVOrdinaryBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ kind x :=
  surjectiveDescent_apply _ _ _ _ x

def gradedEvaluation (kind : EulerKind) :
    GradedRingHom (RVOrdinaryGrading.gradedPiece B) (RESReductionGradings.ordinaryPiece B) :=
  gradedSurjectiveDescent (RVOrdinaryBalancedGradings.coaction B)
    (RVOrdinaryGrading.gradingCoaction B) (RESReductionGradings.ordinaryCoaction B)
    (RVOrdinaryBalancedTensor.comparison B).toRingHom p.surjective
    (fun _ _ hx => (RVOrdinaryBalancedGradings.gradedComparison B).map_mem hx)
    (RVOrdinaryBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ kind).toRingHom
    (kernel_le h00 linear hκ hs B hr hγ hΓ p kind)
    (fun _ _ hx => (RVOrdinaryBalancedGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ kind).map_mem hx)

theorem evaluation_res (kind : EulerKind) (x : RESOrdinaryRing.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ p kind (RVOrdinaryMaps.ofRES B x) =
      RESOrdinaryReduction.quotient B x := by
  have hc : RVOrdinaryBalancedTensor.comparison B (x ⊗ₜ[GammaOrdinaryAlgebras.Coeff B] 1) =
      RVOrdinaryMaps.ofRES B x := by
    rw [RVOrdinaryBalancedTensor.comparison_tmul, map_one, mul_one]
  rw [← hc, evaluation_comparison, RVOrdinaryBalancedTensor.evaluation_res]

def boundedEvaluation (kind : EulerKind) : RVBoundedRing.Ring B →+* RESOrdinaryReduction.ReducedRing B :=
  (evaluation h00 linear hκ hs B hr hγ hΓ p kind).comp (RVOrdinaryMaps.boundedForget B)

def gradedBoundedEvaluation (kind : EulerKind) :
    GradedRingHom (RVBoundedGrading.gradedPiece B) (RESReductionGradings.ordinaryPiece B) :=
  (gradedEvaluation h00 linear hκ hs B hr hγ hΓ p kind).comp (RVOrdinaryMapGradings.gradedBoundedForget B)

theorem boundedEvaluation_res (kind : EulerKind) (x : RESChartRing.Ring B) :
    boundedEvaluation h00 linear hκ hs B hr hγ hΓ p kind (RVBoundedMaps.ofRES B x) =
      RESOrdinaryReduction.forget B x := by
  change evaluation h00 linear hκ hs B hr hγ hΓ p kind
    (RVOrdinaryMaps.boundedForget B (RVBoundedMaps.ofRES B x)) = _
  have he : RVOrdinaryMaps.boundedForget B (RVBoundedMaps.ofRES B x) =
      RVOrdinaryMaps.ofRES B (RESOrdinaryRing.forget B x) :=
    RingHom.congr_fun (RVOrdinaryMaps.boundedForget_ofRES B) x
  rw [he, evaluation_res]
  rfl

theorem boundedEvaluation_pGamma (kind : EulerKind) (γ : Values.Gamma (M := M))
    (hγ' : γ ∈ GammaRVLifts.admissibleRadii B) :
    boundedEvaluation h00 linear hκ hs B hr hγ hΓ p kind (RVRadiusIdeal.pGamma B γ hγ') = 0 := by
  change evaluation h00 linear hκ hs B hr hγ hΓ p kind
    (RVOrdinaryMaps.boundedForget B (RVRadiusIdeal.pGamma B γ hγ')) = 0
  rw [RVOrdinaryRadius.boundedForget_pGamma, map_zero]

theorem radiusIdeal_le_kernel (kind : EulerKind) :
    RVRadiusIdeal.radiusIdeal B ≤ RingHom.ker (boundedEvaluation h00 linear hκ hs B hr hγ hΓ p kind) := by
  intro x hx
  change evaluation h00 linear hκ hs B hr hγ hΓ p kind (RVOrdinaryMaps.boundedForget B x) = 0
  rw [RingHom.mem_ker.mp (RVOrdinaryRadius.radiusIdeal_le_ker B hx), map_zero]

def radiusEvaluation (kind : EulerKind) : RVRadiusQuotient.Ring B →+* RESOrdinaryReduction.ReducedRing B :=
  (evaluation h00 linear hκ hs B hr hγ hΓ p kind).comp (RVOrdinaryRadius.forget B)

def gradedRadiusEvaluation (kind : EulerKind) :
    GradedRingHom (RVRadiusQuotient.piece B) (RESReductionGradings.ordinaryPiece B) :=
  (gradedEvaluation h00 linear hκ hs B hr hγ hΓ p kind).comp (RVOrdinaryMapGradings.gradedRadiusForget B)

theorem radiusEvaluation_quotient (kind : EulerKind) (x : RVBoundedRing.Ring B) :
    radiusEvaluation h00 linear hκ hs B hr hγ hΓ p kind (RVRadiusQuotient.quotient B x) =
      boundedEvaluation h00 linear hκ hs B hr hγ hΓ p kind x := rfl

theorem radiusEvaluation_res (kind : EulerKind) (x : RESChartRing.Ring B) :
    radiusEvaluation h00 linear hκ hs B hr hγ hΓ p kind (RVRadiusQuotient.ofRES B x) =
      RESOrdinaryReduction.forget B x := by
  change evaluation h00 linear hκ hs B hr hγ hΓ p kind
    (RVOrdinaryRadius.forget B (RVRadiusQuotient.ofRES B x)) = _
  have he : RVOrdinaryRadius.forget B (RVRadiusQuotient.ofRES B x) =
      RVOrdinaryMaps.ofRES B (RESOrdinaryRing.forget B x) :=
    RingHom.congr_fun (RVOrdinaryRadius.forget_ofRES B) x
  rw [he, evaluation_res]
  rfl

end DiamondIntegral.Section4.RVT001OrdinaryDescent
