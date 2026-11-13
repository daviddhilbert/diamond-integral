import «section 4».Section3CoefficientChartRelations

/-! Inverse tensor transport on the actual elementary coefficient
objects, including their retained object degrees and full forms. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup
open scoped TensorProduct

namespace DiamondIntegral.Section4.Section3TensorClassTransport
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
attribute [local instance] gammaGroundUnmeasuredTensorGammaRing gammaGroundUnmeasuredTensorFiniteGammaRing
  gammaGroundUnmeasuredTensorRVRing gammaGroundMeasuredTensorGammaRing
  gammaGroundMeasuredTensorFiniteGammaRing gammaGroundMeasuredTensorRVRing

theorem ordinary_symm_tmul (x : Section3RESClassCuts.OrdinaryRing hc B) (y : GammaGroundGammaGrothendieckRing hc B) :
    (Section3TensorRingEquivalences.ordinary hc B).symm (x ⊗ₜ[GammaGroundFiniteGammaGrothendieckRing hc B] y) =
      (Section3RESRingEquivalences.ordinary hc B).symm x ⊗ₜ[GammaOrdinaryFiniteRing.Ring B]
        (Section3GammaRingEquivalences.ordinary hc B).symm y := by
  apply (Section3TensorRingEquivalences.ordinary hc B).injective
  rw [RingEquiv.apply_symm_apply, Section3TensorRingEquivalences.ordinary_tmul,
    RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
theorem measured_symm_tmul (x : Section3RESClassCuts.MeasuredRing hc B) (y : GammaGroundMeasuredGammaGrothendieckRing hc B) :
    (Section3TensorRingEquivalences.measured hc B).symm (x ⊗ₜ[GammaGroundMeasuredFiniteGammaGrothendieckRing hc B] y) =
      (Section3RESRingEquivalences.measured hc B).symm x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B]
        (Section3GammaRingEquivalences.measured hc B).symm y := by
  apply (Section3TensorRingEquivalences.measured hc B).injective
  rw [RingEquiv.apply_symm_apply, Section3TensorRingEquivalences.measured_tmul,
    RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem ordinary_res_symm {r : ℕ} (X : GammaGroundRESObject hc B r) :
    (Section3RESRingEquivalences.ordinary hc B).symm (of (gammaGroundRESDirectSumClass X)) =
      RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES X) := Section3RESRingEquivalences.ordinary_symm_class hc B X
theorem measured_res_symm {r : ℕ} (X : GammaGroundMeasuredRESObject hc B r) :
    (Section3RESRingEquivalences.measured hc B).symm (of (gammaGroundMeasuredRESDirectSumClass X)) =
      RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES X) := Section3RESRingEquivalences.measured_symm_class hc B X

theorem ordinary_gamma_symm {n : ℕ} (G : GammaGroundGammaPiece hc B n) :
    (Section3GammaRingEquivalences.ordinary hc B).symm (of (gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G))) =
      GammaOrdinaryRing.objectClass (Section3GammaChartBridge.chart G) := by
  change (Section3GammaRingEquivalences.ordinary hc B).symm
    (Section3GammaNativeClassCuts.ordinaryClass (GammaGroundGammaObject.single G)) = _
  rw [Section3GammaRingEquivalences.ordinary_symm_class]
  change (∑ _ : Fin 1, GammaOrdinaryRing.objectClass (Section3GammaChartBridge.chart G)) = _
  rw [Fin.sum_univ_one]
theorem measured_gamma_symm {n : ℕ} (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : FullGammaFunction (integrationGammaBase B) f) :
    (Section3GammaRingEquivalences.measured hc B).symm (of (gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf))) =
      GammaRVChartPresentation.objectClass (Section3CoefficientChartRelations.weightChart G f hf) := by
  change (Section3GammaRingEquivalences.measured hc B).symm
    (Section3GammaNativeClassCuts.measuredClass (gammaGroundMeasuredGammaSingleWeight G f hf)) = _
  rw [Section3GammaRingEquivalences.measured_symm_class]
  change (∑ i : Fin 1, GammaRVChartPresentation.objectClass (Section3GammaChartBridge.measuredChart G
    ((gammaGroundMeasuredGammaSingleWeight G f hf).form i))) = _
  rw [Fin.sum_univ_one]
  rfl

theorem ordinary_elementary {r n : ℕ} (X : GammaGroundRESObject hc B r) (G : GammaGroundGammaPiece hc B n) :
    (Section3TensorRingEquivalences.ordinary hc B).symm (gammaGroundUnmeasuredTensorCompletionEquiv
      (of (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass (GammaGroundGammaObject.single G)))) =
      RESOrdinaryRing.objectClass (Section3RVChartBridge.chartRES X) ⊗ₜ[GammaOrdinaryFiniteRing.Ring B]
        GammaOrdinaryRing.objectClass (Section3GammaChartBridge.chart G) := by
  rw [gammaGroundUnmeasuredTensorCompletionEquiv_tmul, ordinary_symm_tmul, ordinary_res_symm, ordinary_gamma_symm]
theorem measured_elementary {r n : ℕ} (X : GammaGroundMeasuredRESObject hc B r) (G : GammaGroundGammaPiece hc B n)
    (f : (Fin n → Values.Gamma (M := M)) → Values.Gamma (M := M)) (hf : FullGammaFunction (integrationGammaBase B) f) :
    (Section3TensorRingEquivalences.measured hc B).symm (gammaGroundMeasuredTensorCompletionEquiv
      (of (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass (gammaGroundMeasuredGammaSingleWeight G f hf)))) =
      RESChartRing.objectClass (Section3MeasuredRVChartBridge.chartRES X) ⊗ₜ[GammaFiniteRVPresentation.ChartRing B]
        GammaRVChartPresentation.objectClass (Section3CoefficientChartRelations.weightChart G f hf) := by
  rw [gammaGroundMeasuredTensorCompletionEquiv_tmul, measured_symm_tmul, measured_res_symm, measured_gamma_symm]

end DiamondIntegral.Section4.Section3TensorClassTransport
