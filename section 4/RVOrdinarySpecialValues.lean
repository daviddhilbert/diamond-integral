import «section 4».RVOrdinaryTensorEvaluation
import «section 4».GammaOrdinarySpecialClasses
import «section 4».RVBalancedSpecialClasses

/-! The ordinary tensor evaluations of the actual P and h preimages.
The affine-line relation is not imposed in this target; the geometric
P value is point plus torus, and the bounded value is the point. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinarySpecialValues
open RVOrdinaryTensorEvaluation RVBalancedSpecialClasses
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem evaluation_p (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (pPreimage B) = RESOrdinaryReduction.pointClass B -
      (k.rayValue : RESOrdinaryReduction.ReducedRing B) * RESOrdinaryReduction.torusClass B := by
  unfold pPreimage RVMeasuredSpecialClasses.pPreimage
  simp only [map_sub, RVFiniteBalancedTensor.fromInteger_tmul, evaluation_tmul, map_one, one_mul, mul_one,
    RESOrdinaryReduction.forget_objectClass]
  exact congrArg (RESOrdinaryReduction.pointClass B - ·) (GammaOrdinarySpecialClasses.evaluation_ray h00 linear hκ hs B hr hγ hΓ k)

theorem evaluation_h (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (hPreimage B) =
      (k.rayValue : RESOrdinaryReduction.ReducedRing B) * RESOrdinaryReduction.torusClass B := by
  unfold hPreimage RVMeasuredSpecialClasses.hPreimage
  rw [RVFiniteBalancedTensor.fromInteger_tmul, evaluation_tmul, map_one, one_mul]
  exact GammaOrdinarySpecialClasses.evaluation_counterweighted h00 linear hκ hs B hr hγ hΓ k

theorem evaluation_p_geometric (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (pPreimage B) =
      RESOrdinaryReduction.pointClass B + RESOrdinaryReduction.torusClass B := by
  simpa only [EulerKind.rayValue, Int.cast_neg, Int.cast_one, neg_one_mul, sub_neg_eq_add] using
    evaluation_p h00 linear hκ hs B hr hγ hΓ EulerKind.geometric

theorem evaluation_p_bounded (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.bounded (pPreimage B) = RESOrdinaryReduction.pointClass B := by
  simpa only [EulerKind.rayValue, Int.cast_zero, zero_mul, sub_zero] using
    evaluation_p h00 linear hκ hs B hr hγ hΓ EulerKind.bounded

end DiamondIntegral.Section4.RVOrdinarySpecialValues
