import «section 4».RVMeasuredTensor
import «section 4».GammaUnaryIdentityProfile

/-! Actual degree-one P and h classes, integer-tensor preimages and their
constructed values. A global RV retraction and nonzero point class are
not asserted by these preimage calculations. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVMeasuredSpecialClasses
open RVMeasuredTensor GammaCounterweightedRay GammaDefinableMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rayChart (B : Base (M := M)) : GammaWeightedCharts.Chart B 1 :=
  GammaChartOperations.ofTotal B 1 positiveRay (positiveRay_definable B) (fun _ => 1)
    (constant_definable B 1 (GammaGroupNames.one_definable_base B))

def counterweightedChart (B : Base (M := M)) : GammaWeightedCharts.Chart B 1 :=
  GammaChartOperations.ofTotal B 1 positiveRay (positiveRay_definable B)
    inverseCoordinate (inverseCoordinate_definable B)

def pClass (B : Base (M := M)) : RVChartRing.Ring B :=
  RVChartRing.objectClass (RESFibreObjects.point B).toChart - RVChartRing.objectClass (RVSharpCharts.sharpChart (rayChart B))

def hClass (B : Base (M := M)) : RVChartRing.Ring B :=
  RVChartRing.objectClass (RVSharpCharts.sharpChart (counterweightedChart B))

def pPreimage (B : Base (M := M)) : Source B :=
  (RESChartRing.objectClass (RESFibreObjects.point B) ⊗ₜ[ℤ] 1) -
    (1 ⊗ₜ[ℤ] GammaRVChartPresentation.objectClass (rayChart B))

def hPreimage (B : Base (M := M)) : Source B :=
  1 ⊗ₜ[ℤ] GammaRVChartPresentation.objectClass (counterweightedChart B)

theorem comparison_pPreimage (B : Base (M := M)) : comparison B (pPreimage B) = pClass B := by
  unfold pPreimage pClass
  rw [map_sub, comparison_tmul, comparison_tmul, map_one, map_one, mul_one, one_mul, RVChartMaps.ofRES_class]
  exact congrArg (RVChartRing.objectClass (RESFibreObjects.point B).toChart - ·)
    (RVSharpRingMap.sharp_class B (rayChart B))

theorem comparison_hPreimage (B : Base (M := M)) : comparison B (hPreimage B) = hClass B := by
  unfold hPreimage hClass
  rw [comparison_tmul, map_one, one_mul]
  exact RVSharpRingMap.sharp_class B (counterweightedChart B)

theorem pClass_mem (B : Base (M := M)) : pClass B ∈ RVGrading.gradedPiece B 1 :=
  (RVGrading.gradedPiece B 1).sub_mem (RVGrading.class_mem B _) (RVGrading.class_mem B _)

theorem hClass_mem (B : Base (M := M)) : hClass B ∈ RVGrading.gradedPiece B 1 := RVGrading.class_mem B _

theorem right_class_evaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ} (a : GammaWeightedCharts.Chart B n) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (1 ⊗ₜ[ℤ] GammaRVChartPresentation.objectClass a) =
      RESUnboundedPsi.psi B k (GammaWeightedCharts.chartPolynomial h00 hκ hs B hr hγ k a) := by
  rw [evaluation_tmul, map_one, one_mul]
  change RESUnboundedPsi.psi B k (GammaRVChartPresentation.interpretation h00 linear hκ hs B hr hγ hΓ k
    (GammaRVChartPresentation.objectClass a)) = _
  exact congrArg (RESUnboundedPsi.psi B k) (GammaRVChartPresentation.interpretation_symbol h00 linear hκ hs B hr hγ hΓ k a)

theorem psi_positiveRay (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ) (k : EulerKind) :
    RESUnboundedPsi.psi B k (GammaObjectPolynomial.objectPolynomial h00 hκ hs B hr hγ k 1 positiveRay
      (positiveRay_definable B) (fun _ => 1) (constant_definable B 1 (GammaGroupNames.one_definable_base B))) =
      RESMeasuredReduction.pointClass B := by
  rw [GammaUnaryIdentityProfile.objectPolynomial_positiveRay]
  have h := RESUnboundedPsi.psi_ray_positive B k 1 (by decide) 0
  simpa [RESUnboundedPsi.weightedPoint_formula] using h

theorem evaluation_pPreimage (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (pPreimage B) = 0 := by
  unfold pPreimage
  rw [map_sub, evaluation_tmul, map_one, mul_one, right_class_evaluation]
  change RESMeasuredReduction.pointClass B - RESUnboundedPsi.psi B k
    (GammaWeightedCharts.chartPolynomial h00 hκ hs B hr hγ k (rayChart B)) = 0
  unfold rayChart
  rw [GammaChartOperations.chartPolynomial_ofTotal, psi_positiveRay, sub_self]

theorem evaluation_hPreimage_geometric (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (hPreimage B) = RESMeasuredReduction.pointClass B := by
  unfold hPreimage
  rw [right_class_evaluation]
  unfold counterweightedChart
  rw [GammaChartOperations.chartPolynomial_ofTotal]
  exact RESUnboundedPsi.psi_counterweighted_geometric h00 hκ hs B hr hγ

theorem evaluation_hPreimage_bounded (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.bounded (hPreimage B) = 0 := by
  unfold hPreimage
  rw [right_class_evaluation]
  unfold counterweightedChart
  rw [GammaChartOperations.chartPolynomial_ofTotal]
  exact RESUnboundedPsi.psi_counterweighted_bounded h00 hκ hs B hr hγ

end DiamondIntegral.Section4.RVMeasuredSpecialClasses
