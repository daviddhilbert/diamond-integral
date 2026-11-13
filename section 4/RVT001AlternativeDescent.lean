import «section 4».ApprovedT001Presentation
import «section 4».CoactionSurjectiveDescent
import «section 4».RVAlternativeTensorEvaluation

/-! Remark 4.8's alternative geometric assignment also identifies the
approved T001 kernel: compensated translations preserve the whole lambda
polynomial before either psi is applied. Its actual RV descent and grading
retain the explicit transported T001 hypothesis. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVT001AlternativeDescent
open PolynomialCoactionGrading.Coaction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem gamma_translated {n : ℕ} (a : Fin n → Values.Gamma (M := M))
    (ha : ∀ i, GammaDefinableClosureAtBase B (a i)) (c : GammaWeightedCharts.Chart B n) :
    GammaAlternativeEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ
        (GammaRVChartPresentation.objectClass c) =
      GammaAlternativeEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ
        (GammaRVChartPresentation.objectClass (GammaTranslationCharts.translatedChart B a ha c)) := by
  change RESAlternativePsi.psi B (GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ
      EulerKind.geometric (GammaRVChartPresentation.objectClass c)) =
    RESAlternativePsi.psi B (GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ
      EulerKind.geometric (GammaRVChartPresentation.objectClass _))
  have hc : GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric
      (GammaRVChartPresentation.objectClass c) =
      GammaWeightedCharts.chartPolynomial h00 hκ hs B hr hγ EulerKind.geometric c :=
    GammaRVChartPresentation.interpretation_symbol h00 linear hκ hs B hr hγ hΓ EulerKind.geometric c
  have hd : GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric
      (GammaRVChartPresentation.objectClass (GammaTranslationCharts.translatedChart B a ha c)) =
      GammaWeightedCharts.chartPolynomial h00 hκ hs B hr hγ EulerKind.geometric
        (GammaTranslationCharts.translatedChart B a ha c) :=
    GammaRVChartPresentation.interpretation_symbol h00 linear hκ hs B hr hγ hΓ EulerKind.geometric _
  rw [hc, hd]
  exact congrArg (RESAlternativePsi.psi B)
    (GammaTranslationCharts.chartPolynomial_translated h00 linear hκ hs B hr hγ hΓ EulerKind.geometric a ha c)

theorem translation_generator_zero {k n : ℕ} (r : RVMeasuredCharts.RESChart B k)
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : GammaWeightedCharts.Chart B n) :
    RVAlternativeTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ
      (RVTranslationIdeals.measuredGenerator B r a ha c) = 0 := by
  unfold RVTranslationIdeals.measuredGenerator
  rw [map_sub, RVAlternativeTensorEvaluation.evaluation_tmul, RVAlternativeTensorEvaluation.evaluation_tmul,
    gamma_translated h00 linear hκ hs B hr hγ hΓ a ha c, sub_self]

theorem translationIdeal_le_kernel : RVTranslationIdeals.measuredIdeal B ≤
    RingHom.ker (RVAlternativeTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ).toRingHom := by
  apply Ideal.span_le.mpr
  rintro x ⟨k, n, r, a, ha, c, rfl⟩
  exact translation_generator_zero h00 linear hκ hs B hr hγ hΓ r a ha c

variable (p : ApprovedT001Presentation.Measured B)

include p in
theorem kernel_le : RingHom.ker (RVFiniteBalancedTensor.comparison B).toRingHom ≤
    RingHom.ker (RVAlternativeTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ).toRingHom :=
  p.kernel_le.trans ((RVCoefficientCoordinateTranslationKernel.coefficientIdeal_le_translationIdeal B).trans
    (translationIdeal_le_kernel h00 linear hκ hs B hr hγ hΓ))

def evaluation : RVChartRing.Ring B →+* RESAlternativeReduction.Ring B :=
  surjectiveDescent (RVFiniteBalancedTensor.comparison B).toRingHom p.surjective
    (RVAlternativeTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ).toRingHom
    (kernel_le h00 linear hκ hs B hr hγ hΓ p)

theorem evaluation_comparison (x : RVFiniteBalancedTensor.Source B) :
    evaluation h00 linear hκ hs B hr hγ hΓ p (RVFiniteBalancedTensor.comparison B x) =
      RVAlternativeTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ x :=
  surjectiveDescent_apply _ _ _ _ x

def gradedEvaluation : GradedRingHom (RVGrading.gradedPiece B) (RESAlternativeReduction.piece B) :=
  gradedSurjectiveDescent (RVBalancedGradings.measuredCoaction B)
    (RVGrading.gradingCoaction B) (RESAlternativeReduction.coaction B)
    (RVFiniteBalancedTensor.comparison B).toRingHom p.surjective
    (fun _ _ hx => (RVBalancedMapGradings.gradedMeasuredComparison B).map_mem hx)
    (RVAlternativeTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ).toRingHom
    (kernel_le h00 linear hκ hs B hr hγ hΓ p)
    (fun _ _ hx => (RVAlternativeTensorEvaluation.gradedEvaluation h00 linear hκ hs B hr hγ hΓ).map_mem hx)

theorem evaluation_res (x : RESChartRing.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ p (RVChartMaps.ofRES B x) =
      RESAlternativeReduction.fromMeasured B x := by
  rw [← RVFiniteBalancedTensor.comparison_res, evaluation_comparison, RVAlternativeTensorEvaluation.evaluation_res]

theorem evaluation_p :
    evaluation h00 linear hκ hs B hr hγ hΓ p (RVMeasuredSpecialClasses.pClass B) = 0 := by
  rw [← RVBalancedSpecialClasses.comparison_pPreimage, evaluation_comparison]
  exact RVAlternativeTensorEvaluation.evaluation_p h00 linear hκ hs B hr hγ hΓ

theorem evaluation_h :
    evaluation h00 linear hκ hs B hr hγ hΓ p (RVMeasuredSpecialClasses.hClass B) =
      RESAlternativeReduction.pointClass B := by
  rw [← RVBalancedSpecialClasses.comparison_hPreimage, evaluation_comparison]
  exact RVAlternativeTensorEvaluation.evaluation_h h00 linear hκ hs B hr hγ hΓ

end DiamondIntegral.Section4.RVT001AlternativeDescent
