import «section 4».RVVolumeIsoEvaluation
import «section 4».GammaBoundedTranslationCharts

/-! Actual compensated Gamma-translation differences vanish under both
finite-Gamma-balanced tensor evaluations. Translation constants need only
be Gamma-definable; a definable RV lift is not assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVTranslationEvaluation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem measured_difference (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (r : RESChartRing.Ring B) (a : Fin n → Values.Gamma (M := M))
    (ha : ∀ i, GammaDefinableClosureAtBase B (a i)) (c : GammaWeightedCharts.Chart B n) :
    RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k
      (r ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] GammaRVChartPresentation.objectClass c -
        r ⊗ₜ[GammaFiniteRVPresentation.ChartRing B]
          GammaRVChartPresentation.objectClass (GammaTranslationCharts.translatedChart B a ha c)) = 0 :=
  RVVolumeIsoEvaluation.unbounded_tensor_difference h00 linear hκ hs B hr hγ hΓ k r c
    (GammaTranslationCharts.translatedChart B a ha c) (GammaTranslationCharts.translationVolumeIso B a ha c)

theorem bounded_difference (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (r : RESChartRing.Ring B) (a : Fin n → Values.Gamma (M := M))
    (ha : ∀ i, GammaDefinableClosureAtBase B (a i)) (c : GammaBoundedRVCharts.BoundedChart B n) :
    RVBoundedBalancedTensor.evaluation hc h00 linear hκ hs B hr hγ hΓ k
      (r ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] GammaBoundedRVPresentation.objectClass c -
        r ⊗ₜ[GammaFiniteRVPresentation.ChartRing B]
          GammaBoundedRVPresentation.objectClass (GammaBoundedTranslationCharts.translatedChart B a ha c)) = 0 :=
  RVVolumeIsoEvaluation.bounded_tensor_difference hc h00 linear hκ hs B hr hγ hΓ k r c
    (GammaBoundedTranslationCharts.translatedChart B a ha c) (GammaBoundedTranslationCharts.translationVolumeIso B a ha c)

end DiamondIntegral.Section4.RVTranslationEvaluation
