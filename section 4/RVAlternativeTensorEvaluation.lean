import «section 4».GammaAlternativeEvaluation
import «section 4».RVBalancedMapGradings
import «section 4».RVBalancedSpecialClasses
import «section 4».GammaOrdinarySpecialClasses

/-! The alternative geometric map on the actual tensor balanced over
finite Gamma. Its grading, RES restriction and P/h values are proved.
Descent through the complete RV comparison kernel remains separate. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVAlternativeTensorEvaluation
open RESAlternativeReduction
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

instance targetAlgebra (B : Base (M := M)) : Algebra (GammaFiniteRVPresentation.ChartRing B) (Ring B) :=
  (GammaAlternativeEvaluation.resMap B).toAlgebra

def resEvaluation (B : Base (M := M)) : RESChartRing.Ring B →ₐ[GammaFiniteRVPresentation.ChartRing B] Ring B where
  toRingHom := fromMeasured B
  commutes' _ := rfl

variable (h00 : M ⊨ Axioms.ACVF00)
  (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
  (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
  (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
  (hΓ : Section2.NontrivialDefinableGamma B)

def gammaEvaluation : GammaRVChartPresentation.ChartRing B →ₐ[GammaFiniteRVPresentation.ChartRing B] Ring B where
  toRingHom := GammaAlternativeEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ
  commutes' c := (RingHom.congr_fun (GammaAlternativeEvaluation.finite_balance h00 linear hκ hs B hr hγ hΓ) c).symm

def evaluation : RVFiniteBalancedTensor.Source B →ₐ[GammaFiniteRVPresentation.ChartRing B] Ring B :=
  Algebra.TensorProduct.lift (resEvaluation B) (gammaEvaluation h00 linear hκ hs B hr hγ hΓ)
    (fun _ _ => Commute.all _ _)

theorem evaluation_tmul (x : RESChartRing.Ring B) (y : GammaRVChartPresentation.ChartRing B) :
    evaluation h00 linear hκ hs B hr hγ hΓ (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) =
      fromMeasured B x * GammaAlternativeEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ y := rfl

def gradedEvaluation : GradedRingHom (RVBalancedGradings.measuredPiece B) (piece B) :=
  TensorGradedMaps.gradedMap (RVBalancedGradings.measuredData B) (coaction B)
    (evaluation h00 linear hκ hs B hr hγ hΓ).toRingHom (by
      intro m n x y hx hy
      change evaluation h00 linear hκ hs B hr hγ hΓ (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) ∈ piece B (m + n)
      rw [evaluation_tmul]
      exact SetLike.mul_mem_graded
        (quotient_mem B (RESReductionGradings.measured_quotient_mem B hx))
        ((GammaAlternativeEvaluation.gradedEvaluation h00 linear hκ hs B hr hγ hΓ).map_mem hy))

theorem evaluation_res (x : RESChartRing.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ (RVFiniteBalancedTensor.resInclusion B x) = fromMeasured B x := by
  change evaluation h00 linear hκ hs B hr hγ hΓ (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] 1) = _
  rw [evaluation_tmul, map_one, mul_one]

theorem gamma_ray : GammaAlternativeEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ
    (GammaRVChartPresentation.objectClass (RVMeasuredSpecialClasses.rayChart B)) = -torusClass B := by
  rw [GammaAlternativeEvaluation.evaluation_class_positive h00 linear hκ hs B hr hγ hΓ (by decide : (1 : ℕ) ≠ 0)]
  change (GammaIteratedIntegral.integrateAll h00 hκ hs B hr hγ EulerKind.geometric 1
    (GammaIndicators.indicatorFamily B GammaCounterweightedRay.positiveRay
      (GammaCounterweightedRay.positiveRay_definable B)) : Ring B) * torusClass B ^ 1 = _
  rw [GammaOrdinarySpecialClasses.positiveRay_integral h00 linear hκ hs B hr hγ hΓ EulerKind.geometric,
    pow_one]
  simp only [EulerKind.rayValue, Int.cast_neg, Int.cast_one, neg_one_mul]

theorem gamma_counterweighted : GammaAlternativeEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ
    (GammaRVChartPresentation.objectClass (RVMeasuredSpecialClasses.counterweightedChart B)) = -torusClass B := by
  have he : GammaAlternativeEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ
      (GammaRVChartPresentation.objectClass (RVMeasuredSpecialClasses.counterweightedChart B)) =
      GammaAlternativeEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ
        (GammaRVChartPresentation.objectClass (RVMeasuredSpecialClasses.rayChart B)) := by
    rw [GammaAlternativeEvaluation.evaluation_class_positive h00 linear hκ hs B hr hγ hΓ (by decide : (1 : ℕ) ≠ 0),
      GammaAlternativeEvaluation.evaluation_class_positive h00 linear hκ hs B hr hγ hΓ (by decide : (1 : ℕ) ≠ 0)]
    rfl
  exact he.trans (gamma_ray h00 linear hκ hs B hr hγ hΓ)

theorem evaluation_p : evaluation h00 linear hκ hs B hr hγ hΓ (RVBalancedSpecialClasses.pPreimage B) = 0 := by
  unfold RVBalancedSpecialClasses.pPreimage RVMeasuredSpecialClasses.pPreimage
  simp only [map_sub, RVFiniteBalancedTensor.fromInteger_tmul, evaluation_tmul, map_one, one_mul, mul_one]
  rw [gamma_ray]
  change pointClass B - -torusClass B = 0
  rw [sub_neg_eq_add, add_comm]
  exact torus_plus_point_zero B

theorem evaluation_h : evaluation h00 linear hκ hs B hr hγ hΓ (RVBalancedSpecialClasses.hPreimage B) = pointClass B := by
  unfold RVBalancedSpecialClasses.hPreimage RVMeasuredSpecialClasses.hPreimage
  rw [RVFiniteBalancedTensor.fromInteger_tmul, evaluation_tmul, map_one, one_mul, gamma_counterweighted]
  exact (eq_neg_of_add_eq_zero_right (torus_plus_point_zero B)).symm

end DiamondIntegral.Section4.RVAlternativeTensorEvaluation
