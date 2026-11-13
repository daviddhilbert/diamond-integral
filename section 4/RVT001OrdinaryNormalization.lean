import «section 4».RVT001OrdinaryDescent
import «section 4».RVOrdinaryTensorNormalization

/-! The actual ordinary RV maps normalized by the point and affine-line
classes, relative to the transported approved T001 presentation. Both
factor through the actual RV relation P=1. The bounded map commutes on
the whole radius quotient with forgetting degree after the bounded
measured retraction. No bounded tensor presentation is required. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVT001OrdinaryNormalization
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (p : ApprovedT001Presentation.Ordinary B)

def boundedRaw : RVOrdinaryRing.Ring B →+* RESDimensionFreeReduction.Ring B :=
  (RESDimensionFreeReduction.fromGradedReduced B).comp
    (RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.bounded)

def homogeneousRaw : RVOrdinaryRing.Ring B →+* RESAffineLocalization.Source B :=
  (RESAffineNormalization.normalize B).comp
    (RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.geometric)

theorem boundedRaw_comparison (x : RVOrdinaryBalancedTensor.Source B) :
    boundedRaw h00 linear hκ hs B hr hγ hΓ p (RVOrdinaryBalancedTensor.comparison B x) =
      RVOrdinaryTensorNormalization.boundedRaw h00 linear hκ hs B hr hγ hΓ x := by
  change RESDimensionFreeReduction.fromGradedReduced B
    (RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.bounded
      (RVOrdinaryBalancedTensor.comparison B x)) = _
  rw [RVT001OrdinaryDescent.evaluation_comparison]
  rfl

theorem homogeneousRaw_comparison (x : RVOrdinaryBalancedTensor.Source B) :
    homogeneousRaw h00 linear hκ hs B hr hγ hΓ p (RVOrdinaryBalancedTensor.comparison B x) =
      RVOrdinaryTensorNormalization.homogeneousRaw h00 linear hκ hs B hr hγ hΓ x := by
  change RESAffineNormalization.normalize B
    (RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.geometric
      (RVOrdinaryBalancedTensor.comparison B x)) = _
  rw [RVT001OrdinaryDescent.evaluation_comparison]
  rfl

theorem bounded_p :
    boundedRaw h00 linear hκ hs B hr hγ hΓ p (RVOrdinaryPNormalization.pClass B) = 1 := by
  rw [← RVOrdinaryBalancedSpecialClasses.comparison_pPreimage, boundedRaw_comparison]
  exact RVOrdinaryTensorNormalization.bounded_p h00 linear hκ hs B hr hγ hΓ

theorem homogeneous_p :
    homogeneousRaw h00 linear hκ hs B hr hγ hΓ p (RVOrdinaryPNormalization.pClass B) = 1 := by
  rw [← RVOrdinaryBalancedSpecialClasses.comparison_pPreimage, homogeneousRaw_comparison]
  exact RVOrdinaryTensorNormalization.homogeneous_p h00 linear hκ hs B hr hγ hΓ

theorem bounded_ideal_zero :
    RVOrdinaryPNormalization.pIdeal B ≤ RingHom.ker (boundedRaw h00 linear hκ hs B hr hγ hΓ p) := by
  apply Ideal.span_le.mpr
  rintro x (rfl : x = _)
  change boundedRaw h00 linear hκ hs B hr hγ hΓ p (_ - 1) = 0
  rw [map_sub, map_one, bounded_p, sub_self]

theorem homogeneous_ideal_zero :
    RVOrdinaryPNormalization.pIdeal B ≤ RingHom.ker (homogeneousRaw h00 linear hκ hs B hr hγ hΓ p) := by
  apply Ideal.span_le.mpr
  rintro x (rfl : x = _)
  change homogeneousRaw h00 linear hκ hs B hr hγ hΓ p (_ - 1) = 0
  rw [map_sub, map_one, homogeneous_p, sub_self]

def bounded : RVOrdinaryPNormalization.Ring B →+* RESDimensionFreeReduction.Ring B :=
  Ideal.Quotient.lift _ (boundedRaw h00 linear hκ hs B hr hγ hΓ p)
    (bounded_ideal_zero h00 linear hκ hs B hr hγ hΓ p)

def homogeneous : RVOrdinaryPNormalization.Ring B →+* RESAffineLocalization.Source B :=
  Ideal.Quotient.lift _ (homogeneousRaw h00 linear hκ hs B hr hγ hΓ p)
    (homogeneous_ideal_zero h00 linear hκ hs B hr hγ hΓ p)

def geometric : RVOrdinaryPNormalization.Ring B →+* RESAffineLocalization.Target B :=
  (RESAffineLocalization.comparison B).comp (homogeneous h00 linear hκ hs B hr hγ hΓ p)

theorem bounded_res (x : RESOrdinaryRing.Ring B) :
    bounded h00 linear hκ hs B hr hγ hΓ p (RVOrdinaryPNormalization.ofRES B x) =
      RESDimensionFreeReduction.fromOrdinary B x := by
  change RESDimensionFreeReduction.fromGradedReduced B
    (RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.bounded
      (RVOrdinaryMaps.ofRES B x)) = _
  rw [RVT001OrdinaryDescent.evaluation_res]
  exact RESDimensionFreeReduction.fromGradedReduced_raw B x

theorem homogeneous_res {n : ℕ} (x : RESOrdinaryRing.Ring B)
    (hx : x ∈ RESOrdinaryGrading.gradedPiece B n) :
    homogeneous h00 linear hκ hs B hr hγ hΓ p (RVOrdinaryPNormalization.ofRES B x) =
      RESAffineLocalization.fraction B n (RESOrdinaryReduction.quotient B x)
        (RESReductionGradings.ordinary_quotient_mem B hx) := by
  change RESAffineNormalization.normalize B
    (RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.geometric
      (RVOrdinaryMaps.ofRES B x)) = _
  rw [RVT001OrdinaryDescent.evaluation_res]
  exact RESAffineNormalization.normalize_homogeneous B (RESReductionGradings.ordinary_quotient_mem B hx)

theorem bounded_radius_square :
    (bounded h00 linear hκ hs B hr hγ hΓ p).comp (RVOrdinaryPNormalization.forget B) =
      (RESDimensionFreeReduction.fromGradedReduced B).comp
        (RVT001OrdinaryDescent.radiusEvaluation h00 linear hκ hs B hr hγ hΓ p EulerKind.bounded) := by
  ext x
  rfl

end DiamondIntegral.Section4.RVT001OrdinaryNormalization
