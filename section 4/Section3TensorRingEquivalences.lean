import «section 4».Section3CoefficientSquares
import «section 4».RingTensorCongruence

/-! The actual balanced source tensors in Sections 3 and 4 are
isomorphic through the proved coefficient squares. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
open scoped TensorProduct

namespace DiamondIntegral.Section4.Section3TensorRingEquivalences
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
attribute [local instance] gammaGroundUnmeasuredTensorGammaRing gammaGroundUnmeasuredTensorFiniteGammaRing
  gammaGroundUnmeasuredTensorRVRing gammaGroundMeasuredTensorGammaRing
  gammaGroundMeasuredTensorFiniteGammaRing gammaGroundMeasuredTensorRVRing

def ordinary : RVOrdinaryBalancedTensor.Source B ≃+* GammaGroundUnmeasuredGroupTensor hc B :=
  RingTensorCongruence.congr (Section3FiniteGammaRingEquivalences.ordinary hc B)
    (Section3RESRingEquivalences.ordinary hc B) (Section3GammaRingEquivalences.ordinary hc B)
    (fun r => RingHom.congr_fun (Section3CoefficientSquares.ordinary_res hc B) r)
    (fun r => RingHom.congr_fun (Section3CoefficientSquares.ordinary_gamma hc B) r)

def measured : RVFiniteBalancedTensor.Source B ≃+* GammaGroundMeasuredGroupTensor hc B :=
  RingTensorCongruence.congr (Section3FiniteGammaRingEquivalences.measured hc B)
    (Section3RESRingEquivalences.measured hc B) (Section3GammaRingEquivalences.measured hc B)
    (fun r => RingHom.congr_fun (Section3CoefficientSquares.measured_res hc B) r)
    (fun r => RingHom.congr_fun (Section3CoefficientSquares.measured_gamma hc B) r)

theorem ordinary_tmul (x : RESOrdinaryRing.Ring B) (y : GammaOrdinaryRing.Ring B) :
    ordinary hc B (x ⊗ₜ[GammaOrdinaryFiniteRing.Ring B] y) =
      Section3RESRingEquivalences.ordinary hc B x ⊗ₜ[GammaGroundFiniteGammaGrothendieckRing hc B]
        Section3GammaRingEquivalences.ordinary hc B y := RingTensorCongruence.congr_tmul _ _ _ _ _ _ _
theorem measured_tmul (x : RESChartRing.Ring B) (y : GammaRVChartPresentation.ChartRing B) :
    measured hc B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) =
      Section3RESRingEquivalences.measured hc B x ⊗ₜ[GammaGroundMeasuredFiniteGammaGrothendieckRing hc B]
        Section3GammaRingEquivalences.measured hc B y := RingTensorCongruence.congr_tmul _ _ _ _ _ _ _

end DiamondIntegral.Section4.Section3TensorRingEquivalences
