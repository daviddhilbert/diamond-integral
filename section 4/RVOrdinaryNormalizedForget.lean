import «section 4».RVOrdinaryTensorForget
import «section 4».RVOrdinaryTensorNormalization
import «section 4».RVAffineTensorEvaluation

/-! The ordinary tensor forgetful map takes the actual P preimage to P
and identifies the images of the two P−1 ideals. Its induced quotient map
is surjective. The bounded and affine-normalized geometric constructions
commute with this whole map, before and after quotienting. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinaryNormalizedForget
open RVOrdinaryTensorForget
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem forget_p (B : Base (M := M)) :
    forget B (RVBalancedSpecialClasses.pPreimage B) = RVOrdinaryBalancedSpecialClasses.pPreimage B := by
  unfold RVBalancedSpecialClasses.pPreimage RVMeasuredSpecialClasses.pPreimage
  rw [map_sub, map_sub, RVFiniteBalancedTensor.fromInteger_tmul,
    RVFiniteBalancedTensor.fromInteger_tmul, forget_tmul, forget_tmul,
    map_one, map_one, RESOrdinaryRing.forget_objectClass, GammaOrdinaryRing.forget_class]
  rfl

theorem map_pIdeal (B : Base (M := M)) :
    Ideal.map (forget B) (RVAffineTensorEvaluation.pIdeal B) = RVOrdinaryTensorNormalization.pIdeal B := by
  rw [RVAffineTensorEvaluation.pIdeal, Ideal.map_span, Set.image_singleton,
    map_sub, map_one, forget_p]
  rfl

def quotientRaw (B : Base (M := M)) : RVFiniteBalancedTensor.Source B →+* RVOrdinaryTensorNormalization.Ring B :=
  (RVOrdinaryTensorNormalization.quotient B).comp (forget B)

theorem pIdeal_le_ker (B : Base (M := M)) :
    RVAffineTensorEvaluation.pIdeal B ≤ RingHom.ker (quotientRaw B) := by
  apply Ideal.span_le.mpr
  intro x hx
  have he : x = RVBalancedSpecialClasses.pPreimage B - 1 := hx
  subst x
  change RVOrdinaryTensorNormalization.quotient B (forget B (_ - 1)) = 0
  rw [map_sub, map_one, forget_p]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

def quotientForget (B : Base (M := M)) : RVAffineTensorEvaluation.Ring B →+* RVOrdinaryTensorNormalization.Ring B :=
  Ideal.Quotient.lift _ (quotientRaw B) (pIdeal_le_ker B)

theorem quotientForget_mk (B : Base (M := M)) (x : RVFiniteBalancedTensor.Source B) :
    quotientForget B (RVAffineTensorEvaluation.quotient B x) =
      RVOrdinaryTensorNormalization.quotient B (forget B x) := rfl

theorem quotientForget_surjective (B : Base (M := M)) : Function.Surjective (quotientForget B) := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, rfl⟩ := forget_surjective B z
  exact ⟨RVAffineTensorEvaluation.quotient B x, rfl⟩

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)

theorem bounded_raw_square :
    (RVOrdinaryTensorNormalization.boundedRaw h00 linear hκ hs B hr hγ hΓ).comp (forget B) =
      RVOrdinaryDimensionFreeEvaluation.boundedEvaluation h00 linear hκ hs B hr hγ hΓ := by
  change (RESDimensionFreeReduction.fromGradedReduced B).comp
    ((RVOrdinaryBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.bounded).toRingHom.comp (forget B)) = _
  rw [evaluation_square]
  rfl

theorem homogeneous_raw_square :
    (RVOrdinaryTensorNormalization.homogeneousRaw h00 linear hκ hs B hr hγ hΓ).comp (forget B) =
      RVAffineTensorEvaluation.homogeneousEvaluation h00 linear hκ hs B hr hγ hΓ := by
  change (RESAffineNormalization.normalize B).comp
    ((RVOrdinaryBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ EulerKind.geometric).toRingHom.comp (forget B)) = _
  rw [evaluation_square]
  rfl

theorem geometric_raw_square :
    (RVOrdinaryTensorNormalization.geometricRaw h00 linear hκ hs B hr hγ hΓ).comp (forget B) =
      RVAffineTensorEvaluation.geometricEvaluation h00 linear hκ hs B hr hγ hΓ := by
  change (RESAffineLocalization.comparison B).comp
    ((RVOrdinaryTensorNormalization.homogeneousRaw h00 linear hκ hs B hr hγ hΓ).comp (forget B)) = _
  rw [homogeneous_raw_square]
  rfl

theorem bounded_square :
    (RVOrdinaryTensorNormalization.bounded h00 linear hκ hs B hr hγ hΓ).comp (quotientForget B) =
      RVAffineTensorEvaluation.boundedQuotient h00 linear hκ hs B hr hγ hΓ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  exact RingHom.congr_fun (bounded_raw_square h00 linear hκ hs B hr hγ hΓ) x

theorem homogeneous_square :
    (RVOrdinaryTensorNormalization.homogeneous h00 linear hκ hs B hr hγ hΓ).comp (quotientForget B) =
      RVAffineTensorEvaluation.homogeneousQuotient h00 linear hκ hs B hr hγ hΓ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  exact RingHom.congr_fun (homogeneous_raw_square h00 linear hκ hs B hr hγ hΓ) x

theorem geometric_square :
    (RVOrdinaryTensorNormalization.geometric h00 linear hκ hs B hr hγ hΓ).comp (quotientForget B) =
      RVAffineTensorEvaluation.geometricQuotient h00 linear hκ hs B hr hγ hΓ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  exact RingHom.congr_fun (geometric_raw_square h00 linear hκ hs B hr hγ hΓ) x

end DiamondIntegral.Section4.RVOrdinaryNormalizedForget
