import «section 4».RVOrdinaryBalancedSpecialClasses
import «section 4».RESAffineNormalization

/-! Point-normalized bounded and affine-normalized geometric Euler maps
on the actual ordinary tensor. Both factor through P=1 on that source.
The geometric point value is the inverse dimension-free affine class.
No RV kernel descent or affine-localization injectivity is asserted. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinaryTensorNormalization
open RVOrdinaryBalancedTensor RVOrdinaryBalancedSpecialClasses GammaOrdinaryAlgebras
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def pIdeal (B : Base (M := M)) : Ideal (Source B) := Ideal.span {pPreimage B - 1}
def Ring (B : Base (M := M)) := Source B ⧸ pIdeal B
  deriving CommRing

def quotient (B : Base (M := M)) : Source B →+* Ring B := Ideal.Quotient.mk _

def comparisonRaw (B : Base (M := M)) : Source B →+* RVOrdinaryPNormalization.Ring B :=
  (RVOrdinaryPNormalization.quotient B).comp (RVOrdinaryBalancedTensor.comparison B).toRingHom

theorem comparison_ideal_zero (B : Base (M := M)) : pIdeal B ≤ RingHom.ker (comparisonRaw B) := by
  apply Ideal.span_le.mpr
  intro x hx
  have he : x = pPreimage B - 1 := hx
  subst x
  change comparisonRaw B (_ - 1) = 0
  rw [map_sub, map_one]
  change RVOrdinaryPNormalization.quotient B (RVOrdinaryBalancedTensor.comparison B (pPreimage B)) - 1 = 0
  rw [comparison_pPreimage, RVOrdinaryPNormalization.p_one, sub_self]

def comparison (B : Base (M := M)) : Ring B →+* RVOrdinaryPNormalization.Ring B :=
  Ideal.Quotient.lift _ (comparisonRaw B) (comparison_ideal_zero B)

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

def boundedRaw : Source B →+* RESDimensionFreeReduction.Ring B :=
  (RESDimensionFreeReduction.fromGradedReduced B).comp (evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.bounded).toRingHom

def homogeneousRaw : Source B →+* RESAffineLocalization.Source B :=
  (RESAffineNormalization.normalize B).comp (evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric).toRingHom

def geometricRaw : Source B →+* RESAffineLocalization.Target B :=
  (RESAffineLocalization.comparison B).comp (homogeneousRaw h00 linear hκ hs B hr hγ hΓ)

theorem bounded_p : boundedRaw h00 linear hκ hs B hr hγ hΓ (pPreimage B) = 1 := by
  change RESDimensionFreeReduction.fromGradedReduced B (evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.bounded (pPreimage B)) = 1
  rw [evaluation_p_bounded]
  exact RVOrdinaryDimensionFreeEvaluation.point_value_one B

theorem homogeneous_p : homogeneousRaw h00 linear hκ hs B hr hγ hΓ (pPreimage B) = 1 := by
  change RESAffineNormalization.normalize B (evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (pPreimage B)) = 1
  rw [evaluation_p_geometric, add_comm]
  exact RESAffineNormalization.normalize_affine B

theorem bounded_ideal_zero : pIdeal B ≤ RingHom.ker (boundedRaw h00 linear hκ hs B hr hγ hΓ) := by
  apply Ideal.span_le.mpr
  intro x hx
  have he : x = pPreimage B - 1 := hx
  subst x
  change boundedRaw h00 linear hκ hs B hr hγ hΓ (_ - 1) = 0
  rw [map_sub, map_one, bounded_p, sub_self]

theorem homogeneous_ideal_zero : pIdeal B ≤ RingHom.ker (homogeneousRaw h00 linear hκ hs B hr hγ hΓ) := by
  apply Ideal.span_le.mpr
  intro x hx
  have he : x = pPreimage B - 1 := hx
  subst x
  change homogeneousRaw h00 linear hκ hs B hr hγ hΓ (_ - 1) = 0
  rw [map_sub, map_one, homogeneous_p, sub_self]

def bounded : Ring B →+* RESDimensionFreeReduction.Ring B :=
  Ideal.Quotient.lift _ (boundedRaw h00 linear hκ hs B hr hγ hΓ) (bounded_ideal_zero h00 linear hκ hs B hr hγ hΓ)
def homogeneous : Ring B →+* RESAffineLocalization.Source B :=
  Ideal.Quotient.lift _ (homogeneousRaw h00 linear hκ hs B hr hγ hΓ) (homogeneous_ideal_zero h00 linear hκ hs B hr hγ hΓ)
def geometric : Ring B →+* RESAffineLocalization.Target B :=
  (RESAffineLocalization.comparison B).comp (homogeneous h00 linear hκ hs B hr hγ hΓ)

theorem bounded_point : bounded h00 linear hκ hs B hr hγ hΓ (quotient B (pointPreimage B)) = 1 := by
  change RESDimensionFreeReduction.fromGradedReduced B (evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.bounded (pointPreimage B)) = 1
  rw [evaluation_point]
  exact RVOrdinaryDimensionFreeEvaluation.point_value_one B

theorem geometric_point : geometric h00 linear hκ hs B hr hγ hΓ (quotient B (pointPreimage B)) =
    IsLocalization.Away.invSelf (RESAffineLocalization.dimensionFreeAffine B) := by
  change RESAffineLocalization.comparison B (RESAffineNormalization.normalize B
    (evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (pointPreimage B))) = _
  rw [evaluation_point]
  exact RESAffineNormalization.comparison_point B

theorem bounded_res (x : RESOrdinaryRing.Ring B) :
    bounded h00 linear hκ hs B hr hγ hΓ (quotient B (x ⊗ₜ[Coeff B] 1)) = RESDimensionFreeReduction.fromOrdinary B x := by
  change RESDimensionFreeReduction.fromGradedReduced B (evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.bounded (x ⊗ₜ[Coeff B] 1)) = _
  rw [evaluation_res]
  exact RESDimensionFreeReduction.fromGradedReduced_raw B x

theorem homogeneous_res {n : ℕ} (x : RESOrdinaryRing.Ring B) (hx : x ∈ RESOrdinaryGrading.gradedPiece B n) :
    homogeneous h00 linear hκ hs B hr hγ hΓ (quotient B (x ⊗ₜ[Coeff B] 1)) =
      RESAffineLocalization.fraction B n (RESOrdinaryReduction.quotient B x) (RESReductionGradings.ordinary_quotient_mem B hx) := by
  change RESAffineNormalization.normalize B (evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric (x ⊗ₜ[Coeff B] 1)) = _
  rw [evaluation_res]
  exact RESAffineNormalization.normalize_homogeneous B (RESReductionGradings.ordinary_quotient_mem B hx)

end DiamondIntegral.Section4.RVOrdinaryTensorNormalization
