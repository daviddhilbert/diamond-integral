import «section 3».TensorRingDescent
import «section 4».ApprovedT001Presentation

/-! Audit boundary between the finalized Section 3 categorical rings and
the independently constructed Section 4 chart rings. The upstream kernel
theorems supply the Section 4 presentation inputs once the actual ring
equivalences, comparison squares and elementary-pair transport are provided.
The transport data are explicit; this file does not assert their existence. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3 Algebra.GrothendieckAddGroup

namespace DiamondIntegral.Section4.Section3PresentationAudit
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] gammaGroundUnmeasuredTensorGammaRing gammaGroundUnmeasuredTensorFiniteGammaRing
  gammaGroundUnmeasuredTensorRVRing gammaGroundMeasuredTensorGammaRing
  gammaGroundMeasuredTensorFiniteGammaRing gammaGroundMeasuredTensorRVRing

structure OrdinaryTransport (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) where
  source : RVOrdinaryBalancedTensor.Source B ≃+* GammaGroundUnmeasuredGroupTensor hc B
  target : RVOrdinaryRing.Ring B ≃+* GammaGroundRVGrothendieckRing hc B
  comparison : ∀ x, gammaGroundUnmeasuredGroupTensorMap (source x) =
    target (RVOrdinaryBalancedTensor.comparison B x)
  pair : ∀ a b, gammaGroundUnmeasuredCoefficientPair a b →
    source.symm (gammaGroundUnmeasuredTensorCompletionEquiv (of a) -
      gammaGroundUnmeasuredTensorCompletionEquiv (of b)) ∈
        RVOrdinaryCoefficientTranslationKernel.coefficientIdeal B

structure MeasuredTransport (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M)) where
  source : RVFiniteBalancedTensor.Source B ≃+* GammaGroundMeasuredGroupTensor hc B
  target : RVChartRing.Ring B ≃+* GammaGroundMeasuredRVGrothendieckRing hc B
  comparison : ∀ x, gammaGroundMeasuredGroupTensorMap (source x) =
    target (RVFiniteBalancedTensor.comparison B x)
  pair : ∀ a b, gammaGroundMeasuredCoefficientPair a b →
    source.symm (gammaGroundMeasuredTensorCompletionEquiv (of a) -
      gammaGroundMeasuredTensorCompletionEquiv (of b)) ∈
        RVCoefficientCoordinateTranslationKernel.coefficientIdeal B

variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
  {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
  (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
  (hΓ : Section2.NontrivialDefinableGamma B)

def ordinary (T : OrdinaryTransport hc B) : ApprovedT001Presentation.Ordinary B where
  surjective y := by
    obtain ⟨z, hz⟩ := gammaGroundUnmeasuredGroupTensorMap_surjective hκ hs h00 hr hγ hΓ (T.target y)
    refine ⟨T.source.symm z, T.target.injective ?_⟩
    rw [← T.comparison, T.source.apply_symm_apply]
    exact hz
  kernel_le := by
    have hI : gammaGroundUnmeasuredTensorRelationIdeal (hc := hc) (B := B) ≤
        Ideal.comap T.source.symm.toRingHom (RVOrdinaryCoefficientTranslationKernel.coefficientIdeal B) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨a, b, hab, rfl⟩
      exact T.pair a b hab
    intro x hx
    have hm : T.source x ∈ gammaGroundUnmeasuredTensorRelationIdeal (hc := hc) (B := B) := by
      rw [← gammaGroundUnmeasuredGroupTensor_kernel hκ hs h00 hr hγ hΓ]
      change gammaGroundUnmeasuredGroupTensorMap (T.source x) = 0
      rw [T.comparison]
      change RVOrdinaryBalancedTensor.comparison B x = 0 at hx
      rw [hx, map_zero]
    have hh := hI hm
    change T.source.symm (T.source x) ∈ RVOrdinaryCoefficientTranslationKernel.coefficientIdeal B at hh
    simpa only [T.source.symm_apply_apply] using hh

def measured (T : MeasuredTransport hc B) : ApprovedT001Presentation.Measured B where
  surjective y := by
    obtain ⟨z, hz⟩ := gammaGroundMeasuredGroupTensorMap_surjective hκ hs h00 hr hγ hΓ (T.target y)
    refine ⟨T.source.symm z, T.target.injective ?_⟩
    rw [← T.comparison, T.source.apply_symm_apply]
    exact hz
  kernel_le := by
    have hI : gammaGroundMeasuredTensorRelationIdeal (hc := hc) (B := B) ≤
        Ideal.comap T.source.symm.toRingHom (RVCoefficientCoordinateTranslationKernel.coefficientIdeal B) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨a, b, hab, rfl⟩
      exact T.pair a b hab
    intro x hx
    have hm : T.source x ∈ gammaGroundMeasuredTensorRelationIdeal (hc := hc) (B := B) := by
      rw [← gammaGroundMeasuredGroupTensor_kernel hκ hs h00 hr hγ hΓ]
      change gammaGroundMeasuredGroupTensorMap (T.source x) = 0
      rw [T.comparison]
      change RVFiniteBalancedTensor.comparison B x = 0 at hx
      rw [hx, map_zero]
    have hh := hI hm
    change T.source.symm (T.source x) ∈ RVCoefficientCoordinateTranslationKernel.coefficientIdeal B at hh
    simpa only [T.source.symm_apply_apply] using hh

end DiamondIntegral.Section4.Section3PresentationAudit
