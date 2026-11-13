import «section 4».RESAffineNormalization

/-! The geometric Euler map on the actual balanced tensor is normalized
by affine degree and lands in the homogeneous affine localization, then
in the affine localization after forgetting degree. Both it and the
bounded map factor through the actual P−1 tensor relation. Global RV
descent is not asserted. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVAffineTensorEvaluation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pIdeal (B : Base (M := M)) : Ideal (RVFiniteBalancedTensor.Source B) :=
  Ideal.span {RVBalancedSpecialClasses.pPreimage B - 1}

def Ring (B : Base (M := M)) := RVFiniteBalancedTensor.Source B ⧸ pIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : RVFiniteBalancedTensor.Source B →+* Ring B := Ideal.Quotient.mk (pIdeal B)

variable (h00 : M ⊨ Axioms.ACVF00)
  (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
  (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
  (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
  (hΓ : Section2.NontrivialDefinableGamma B)

def homogeneousEvaluation : RVFiniteBalancedTensor.Source B →+* RESAffineLocalization.Source B :=
  (RESAffineNormalization.normalize B).comp
    (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric).toRingHom

def geometricEvaluation : RVFiniteBalancedTensor.Source B →+* RESAffineLocalization.Target B :=
  (RESAffineLocalization.comparison B).comp (homogeneousEvaluation h00 linear hκ hs B hr hγ hΓ)

theorem homogeneous_p : homogeneousEvaluation h00 linear hκ hs B hr hγ hΓ (RVBalancedSpecialClasses.pPreimage B) = 1 := by
  change RESAffineNormalization.normalize B
    (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (RVBalancedSpecialClasses.pPreimage B)) = 1
  rw [RVOrdinarySpecialValues.evaluation_p_geometric, add_comm]
  exact RESAffineNormalization.normalize_affine B

theorem pIdeal_le_homogeneous_ker : pIdeal B ≤ RingHom.ker (homogeneousEvaluation h00 linear hκ hs B hr hγ hΓ) := by
  apply Ideal.span_le.mpr
  intro x hx
  have he : x = RVBalancedSpecialClasses.pPreimage B - 1 := hx
  subst x
  change homogeneousEvaluation h00 linear hκ hs B hr hγ hΓ (_ - 1) = 0
  rw [map_sub, map_one, homogeneous_p, sub_self]

def homogeneousQuotient : Ring B →+* RESAffineLocalization.Source B :=
  Ideal.Quotient.lift _ (homogeneousEvaluation h00 linear hκ hs B hr hγ hΓ)
    (pIdeal_le_homogeneous_ker h00 linear hκ hs B hr hγ hΓ)

def geometricQuotient : Ring B →+* RESAffineLocalization.Target B :=
  (RESAffineLocalization.comparison B).comp (homogeneousQuotient h00 linear hκ hs B hr hγ hΓ)

theorem geometricQuotient_apply (x : RVFiniteBalancedTensor.Source B) :
    geometricQuotient h00 linear hκ hs B hr hγ hΓ (quotient B x) =
      geometricEvaluation h00 linear hκ hs B hr hγ hΓ x := rfl

theorem pIdeal_le_bounded_ker : pIdeal B ≤ RingHom.ker
    (RVOrdinaryDimensionFreeEvaluation.boundedEvaluation h00 linear hκ hs B hr hγ hΓ) := by
  apply Ideal.span_le.mpr
  intro x hx
  have he : x = RVBalancedSpecialClasses.pPreimage B - 1 := hx
  subst x
  exact RVOrdinaryDimensionFreeEvaluation.bounded_p_minus_one h00 linear hκ hs B hr hγ hΓ

def boundedQuotient : Ring B →+* RESDimensionFreeReduction.Ring B :=
  Ideal.Quotient.lift _ (RVOrdinaryDimensionFreeEvaluation.boundedEvaluation h00 linear hκ hs B hr hγ hΓ)
    (pIdeal_le_bounded_ker h00 linear hκ hs B hr hγ hΓ)

theorem boundedQuotient_apply (x : RVFiniteBalancedTensor.Source B) :
    boundedQuotient h00 linear hκ hs B hr hγ hΓ (quotient B x) =
      RVOrdinaryDimensionFreeEvaluation.boundedEvaluation h00 linear hκ hs B hr hγ hΓ x := rfl

theorem homogeneous_res {n : ℕ} (x : RESChartRing.Ring B) (hx : x ∈ RESRingCoaction.gradedPiece B n) :
    homogeneousEvaluation h00 linear hκ hs B hr hγ hΓ (RVFiniteBalancedTensor.resInclusion B x) =
      RESAffineLocalization.fraction B n (RESOrdinaryReduction.forget B x) (RESReductionGradings.forget_mem B hx) := by
  change RESAffineNormalization.normalize B
    (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (RVFiniteBalancedTensor.resInclusion B x)) = _
  rw [RVOrdinaryTensorEvaluation.evaluation_res]
  exact RESAffineNormalization.normalize_homogeneous B (RESReductionGradings.forget_mem B hx)

theorem geometric_point : geometricEvaluation h00 linear hκ hs B hr hγ hΓ
    (RVFiniteBalancedTensor.resInclusion B (RESChartRing.objectClass (RESFibreObjects.point B))) =
      IsLocalization.Away.invSelf (RESAffineLocalization.dimensionFreeAffine B) := by
  change RESAffineLocalization.comparison B (RESAffineNormalization.normalize B
    (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric
      (RVFiniteBalancedTensor.resInclusion B (RESChartRing.objectClass (RESFibreObjects.point B))))) = _
  rw [RVOrdinaryTensorEvaluation.evaluation_res, RESOrdinaryReduction.forget_objectClass]
  exact RESAffineNormalization.comparison_point B

theorem bounded_point : RVOrdinaryDimensionFreeEvaluation.boundedEvaluation h00 linear hκ hs B hr hγ hΓ
    (RVFiniteBalancedTensor.resInclusion B (RESChartRing.objectClass (RESFibreObjects.point B))) = 1 := by
  rw [RVOrdinaryDimensionFreeEvaluation.boundedEvaluation, RVOrdinaryDimensionFreeEvaluation.baseEvaluation_res,
    RESOrdinaryReduction.forget_objectClass]
  exact RVOrdinaryDimensionFreeEvaluation.point_value_one B

end DiamondIntegral.Section4.RVAffineTensorEvaluation
