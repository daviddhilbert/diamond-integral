import «section 4».RVT001OrdinaryNormalization
import «section 4».RESAffineSeparation

/-! The ordinary normalized geometric and bounded maps differ after
mapping the bounded target to the same affine localization. This uses
proved affine separation and retains only the explicit T001 transport. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVT001NormalizedDistinct
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
variable (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (p : ApprovedT001Presentation.Ordinary B)

def boundedInAffine : RVOrdinaryPNormalization.Ring B →+* RESAffineLocalization.Target B :=
  (algebraMap (RESDimensionFreeReduction.Ring B) (RESAffineLocalization.Target B)).comp
    (RVT001OrdinaryNormalization.bounded h00 linear hκ hs B hr hγ hΓ p)

theorem bounded_point : boundedInAffine h00 linear hκ hs B hr hγ hΓ p
    (RVOrdinaryPNormalization.ofRES B (RESOrdinaryRing.objectClass (RESFibreObjects.point B))) = 1 := by
  change algebraMap (RESDimensionFreeReduction.Ring B) (RESAffineLocalization.Target B)
    (RVT001OrdinaryNormalization.bounded h00 linear hκ hs B hr hγ hΓ p
      (RVOrdinaryPNormalization.ofRES B (RESOrdinaryRing.objectClass (RESFibreObjects.point B)))) = 1
  rw [RVT001OrdinaryNormalization.bounded_res]
  have he : RESDimensionFreeReduction.fromOrdinary B (RESOrdinaryRing.objectClass (RESFibreObjects.point B)) = 1 :=
    RVOrdinaryDimensionFreeEvaluation.point_value_one B
  rw [he, map_one]

include hc in
theorem geometric_point_ne_one : RVT001OrdinaryNormalization.geometric h00 linear hκ hs B hr hγ hΓ p
    (RVOrdinaryPNormalization.ofRES B (RESOrdinaryRing.objectClass (RESFibreObjects.point B))) ≠ 1 := by
  change RESAffineLocalization.comparison B (RESAffineNormalization.normalize B
    (RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p .geometric
      (RVOrdinaryMaps.ofRES B (RESOrdinaryRing.objectClass (RESFibreObjects.point B))))) ≠ 1
  rw [RVT001OrdinaryDescent.evaluation_res]
  exact RESAffineSeparation.comparison_point_ne_one_acvf00 hc B h00

include hc in
theorem normalized_maps_distinct : RVT001OrdinaryNormalization.geometric h00 linear hκ hs B hr hγ hΓ p ≠
    boundedInAffine h00 linear hκ hs B hr hγ hΓ p := by
  intro he
  have hv := RingHom.congr_fun he
    (RVOrdinaryPNormalization.ofRES B (RESOrdinaryRing.objectClass (RESFibreObjects.point B)))
  rw [bounded_point] at hv
  exact geometric_point_ne_one hc h00 linear hκ hs B hr hγ hΓ p hv

end DiamondIntegral.Section4.RVT001NormalizedDistinct
