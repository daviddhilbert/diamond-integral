import «section 4».RVOrdinarySpecialValues
import «section 4».RESDimensionFreeReduction
import «section 4».GammaEulerPolynomialMaps

/-! Ordinary Euler maps on the actual full balanced tensor, after
forgetting target degree. The bounded map kills P-1. The geometric map
does so after imposing affine-line class one, and kills every homogeneous
positive-degree Gamma input. These are tensor maps, not global RV descent. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinaryDimensionFreeEvaluation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem point_value_one (B : Base (M := M)) :
    RESDimensionFreeReduction.fromGradedReduced B (RESOrdinaryReduction.pointClass B) = 1 := by
  have hm : RESDimensionFreeReduction.pointClass B - 1 ∈ RESDimensionFreeReduction.pointIdeal B :=
    Ideal.subset_span (Set.mem_singleton _)
  have he : RESDimensionFreeReduction.fromGradedReduced B (RESDimensionFreeReduction.pointClass B - 1) = 0 := by
    change RESDimensionFreeReduction.pointClass B - 1 ∈ RingHom.ker (RESDimensionFreeReduction.fromGradedReduced B)
    rw [RESDimensionFreeReduction.kernel_fromGradedReduced]
    exact hm
  rw [map_sub, map_one] at he
  exact sub_eq_zero.mp he

def torusClass (B : Base (M := M)) : RESDimensionFreeReduction.Ring B :=
  RESDimensionFreeReduction.fromGradedReduced B (RESOrdinaryReduction.torusClass B)

def affineClass (B : Base (M := M)) : RESDimensionFreeReduction.Ring B :=
  RESDimensionFreeReduction.fromGradedReduced B (RESOrdinaryReduction.torusClass B + RESOrdinaryReduction.pointClass B)

theorem affineClass_eq (B : Base (M := M)) : affineClass B = torusClass B + 1 := by
  unfold affineClass
  rw [map_add, point_value_one]
  rfl

def geometricIdeal (B : Base (M := M)) : Ideal (RESDimensionFreeReduction.Ring B) := Ideal.span {affineClass B - 1}

def GeometricRing (B : Base (M := M)) := RESDimensionFreeReduction.Ring B ⧸ geometricIdeal B
  deriving CommRing

def geometricQuotient (B : Base (M := M)) : RESDimensionFreeReduction.Ring B →+* GeometricRing B :=
  Ideal.Quotient.mk (geometricIdeal B)

theorem geometric_torus_zero (B : Base (M := M)) : geometricQuotient B (torusClass B) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have he : affineClass B - 1 ∈ geometricIdeal B := Ideal.subset_span (Set.mem_singleton _)
  simpa only [affineClass_eq, add_sub_cancel_right] using he

def baseEvaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    RVFiniteBalancedTensor.Source B →+* RESDimensionFreeReduction.Ring B :=
  (RESDimensionFreeReduction.fromGradedReduced B).comp
    (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom

def boundedEvaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) : RVFiniteBalancedTensor.Source B →+* RESDimensionFreeReduction.Ring B :=
  baseEvaluation h00 linear hκ hs B hr hγ hΓ EulerKind.bounded

def geometricEvaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) : RVFiniteBalancedTensor.Source B →+* GeometricRing B :=
  (geometricQuotient B).comp (baseEvaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric)

theorem baseEvaluation_res (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (x : RESChartRing.Ring B) :
    baseEvaluation h00 linear hκ hs B hr hγ hΓ k (RVFiniteBalancedTensor.resInclusion B x) =
      RESDimensionFreeReduction.fromGradedReduced B (RESOrdinaryReduction.forget B x) :=
  congrArg (RESDimensionFreeReduction.fromGradedReduced B)
    (RVOrdinaryTensorEvaluation.evaluation_res h00 linear hκ hs B hr hγ hΓ k x)

theorem bounded_p_minus_one (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    boundedEvaluation h00 linear hκ hs B hr hγ hΓ (RVBalancedSpecialClasses.pPreimage B - 1) = 0 := by
  change RESDimensionFreeReduction.fromGradedReduced B
    (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.bounded
      (RVBalancedSpecialClasses.pPreimage B - 1)) = 0
  simp only [map_sub, map_one, RVOrdinarySpecialValues.evaluation_p_bounded, point_value_one, sub_self]

theorem geometric_p_minus_one (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    geometricEvaluation h00 linear hκ hs B hr hγ hΓ (RVBalancedSpecialClasses.pPreimage B - 1) = 0 := by
  have he : baseEvaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric
      (RVBalancedSpecialClasses.pPreimage B - 1) = torusClass B := by
    change RESDimensionFreeReduction.fromGradedReduced B
      (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric
        (RVBalancedSpecialClasses.pPreimage B - 1)) = _
    simp only [map_sub, map_one, RVOrdinarySpecialValues.evaluation_p_geometric, map_add, point_value_one]
    change 1 + torusClass B - 1 = torusClass B
    abel
  change geometricQuotient B (baseEvaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric
    (RVBalancedSpecialClasses.pPreimage B - 1)) = 0
  rw [he, geometric_torus_zero]

theorem geometric_positive_gamma (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {n : ℕ} (hn : n ≠ 0)
    (x : GammaRVChartPresentation.ChartRing B) (hx : x ∈ GammaRVGrading.gradedPiece B n) :
    geometricEvaluation h00 linear hκ hs B hr hγ hΓ (RVFiniteBalancedTensor.gammaInclusion B x) = 0 := by
  let g := (geometricQuotient B).comp (RESDimensionFreeReduction.fromGradedReduced B)
  let p := GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric x
  have hp : p ∈ GammaPolynomialGradings.unboundedPiece B EulerKind.geometric n :=
    (GammaRVMapGradings.gradedInterpretation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric).map_mem hx
  have ht : g (RESOrdinaryReduction.torusClass B) = 0 := geometric_torus_zero B
  change g (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric
    (1 ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] x)) = 0
  rw [RVOrdinaryTensorEvaluation.evaluation_tmul, map_one, one_mul]
  change g (GammaEulerEvaluation.polynomial B EulerKind.geometric (RESOrdinaryReduction.torusClass B) p) = 0
  exact (GammaEulerEvaluation.polynomial_map B EulerKind.geometric g (RESOrdinaryReduction.torusClass B) p).trans
    ((congrArg (fun t => GammaEulerEvaluation.polynomial B EulerKind.geometric t p) ht).trans
      (GammaEulerEvaluation.polynomial_zero_of_mem B EulerKind.geometric hn p hp))

end DiamondIntegral.Section4.RVOrdinaryDimensionFreeEvaluation
