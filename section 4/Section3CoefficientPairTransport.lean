import «section 4».Section3TensorClassTransport
import «section 4».Section3CoefficientFunctionBridge
import «section 4».Section3PresentationAudit

/-! Every explicit native elementary coefficient pair pulls back into
the actual chart coefficient ideal, through its definable coefficient
function. No additional translation generator is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup
open scoped TensorProduct

namespace DiamondIntegral.Section4.Section3CoefficientPairTransport
open Section3TensorClassTransport Section3CoefficientChartRelations Section3CoefficientFunctionBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
attribute [local instance] gammaGroundUnmeasuredTensorGammaRing gammaGroundUnmeasuredTensorFiniteGammaRing
  gammaGroundUnmeasuredTensorRVRing gammaGroundMeasuredTensorGammaRing
  gammaGroundMeasuredTensorFiniteGammaRing gammaGroundMeasuredTensorRVRing

theorem ordinary (a b : GammaGroundUnmeasuredPositiveTensor hc B) (hab : gammaGroundUnmeasuredCoefficientPair a b) :
    (Section3TensorRingEquivalences.ordinary hc B).symm (gammaGroundUnmeasuredTensorCompletionEquiv (of a) -
      gammaGroundUnmeasuredTensorCompletionEquiv (of b)) ∈ RVOrdinaryCoefficientTranslationKernel.coefficientIdeal B := by
  obtain ⟨r, n, i, X, G, H, delta, hsupport, hd, ⟨c, hcval⟩, hs, rfl, rfl⟩ := hab
  have hsub := (Section3TensorRingEquivalences.ordinary hc B).symm.map_sub
    (gammaGroundUnmeasuredTensorCompletionEquiv (of (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G))))
    (gammaGroundUnmeasuredTensorCompletionEquiv (of (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass (GammaGroundGammaObject.single H))))
  rw [hsub, ordinary_elementary, ordinary_elementary]
  let R := Section3RVChartBridge.chartRES X
  have hg : DefinableOverBase B (fun _ : Fin (1 + R.arity) => .rv)
      (RVDefinableGraphExtension.domain R.toChart (function c i)) := function_graph c i
  have hm := RVOrdinaryCoefficientTranslationKernel.function_generator_mem B R (function c i) hg
    (function_nonzero c i) (delta i) (function_value c delta hcval i) (hd i) i (Section3GammaChartBridge.chart G)
  have hv := shiftVector_eq i delta hsupport
  have hm' : RVOrdinaryTranslationIdeal.generator B R delta hd (Section3GammaChartBridge.chart G) ∈
      RVOrdinaryCoefficientTranslationKernel.coefficientIdeal B := by simpa only [hv] using hm
  rw [← ordinary_translated G H delta hd hs]
  exact hm'

theorem measured (a b : GammaGroundMeasuredPositiveTensor hc B) (hab : gammaGroundMeasuredCoefficientPair a b) :
    (Section3TensorRingEquivalences.measured hc B).symm (gammaGroundMeasuredTensorCompletionEquiv (of a) -
      gammaGroundMeasuredTensorCompletionEquiv (of b)) ∈ RVCoefficientCoordinateTranslationKernel.coefficientIdeal B := by
  obtain ⟨r, n, i, X, G, H, f, h, hf, hh, delta, hsupport, hd, ⟨c, hcval⟩, hs, hw, rfl, rfl⟩ := hab
  have hsub := (Section3TensorRingEquivalences.measured hc B).symm.map_sub
    (gammaGroundMeasuredTensorCompletionEquiv (of (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf))))
    (gammaGroundMeasuredTensorCompletionEquiv (of (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight H h hh))))
  rw [hsub, measured_elementary, measured_elementary]
  let R := Section3MeasuredRVChartBridge.chartRES X
  have hg : DefinableOverBase B (fun _ : Fin (1 + R.arity) => .rv)
      (RVDefinableGraphExtension.domain R.toChart (function c i)) := function_graph c i
  have hm := RVCoefficientFunctionTranslationKernel.measured_generator_mem B R (function c i) hg
    (function_nonzero c i) (delta i) (function_value c delta hcval i) (hd i) i (weightChart G f hf)
  have hv := shiftVector_eq i delta hsupport
  have hm' : RVTranslationIdeals.measuredGenerator B R delta hd (weightChart G f hf) ∈
      RVCoefficientCoordinateTranslationKernel.coefficientIdeal B := by simpa only [hv] using hm
  rw [← measured_translated G H f h hf hh delta hd hs hw]
  exact hm'

end DiamondIntegral.Section4.Section3CoefficientPairTransport
