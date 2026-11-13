import «section 3».TensorRingKernelPresentations
import «section 3».RingPresentationDescent
import «section 3».GammaGroundAnnularPullback
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
open Algebra.GrothendieckAddGroup
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
attribute [local instance] gammaGroundUnmeasuredTensorGammaRing gammaGroundUnmeasuredTensorFiniteGammaRing
  gammaGroundUnmeasuredTensorRVRing gammaGroundMeasuredTensorGammaRing
  gammaGroundMeasuredTensorFiniteGammaRing gammaGroundMeasuredTensorRVRing
variable {V : Type} [CommRing V]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
variable (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)
include hκ hs h00 hsmall hγsmall hΓ

/-- The entire ring kernel is killed exactly when the explicit positive
translation pairs have equal evaluations. -/
theorem gammaGroundUnmeasuredGroupTensor_descends_iff
    (H : GammaGroundUnmeasuredGroupTensor (M := M) hc B →+* V) :
    (∃ D : GammaGroundRVGrothendieckRing (M := M) hc B →+* V,
      D.comp gammaGroundUnmeasuredGroupTensorMap = H) ↔
    ∀ a b, gammaGroundUnmeasuredCoefficientPair a b →
      H (gammaGroundUnmeasuredTensorCompletionEquiv (of a)) =
        H (gammaGroundUnmeasuredTensorCompletionEquiv (of b)) := by
  rw [ringPresentation_descends_iff (gammaGroundUnmeasuredGroupTensorMap (M := M) (hc := hc) (ground := B))
    (gammaGroundUnmeasuredGroupTensorMap_surjective hκ hs h00 hsmall hγsmall hΓ)
    (gammaGroundUnmeasuredTensorRelationIdeal (M := M) (hc := hc) (B := B))
    (gammaGroundUnmeasuredGroupTensor_kernel hκ hs h00 hsmall hγsmall hΓ) H]
  exact transportedRelationIdeal_le_kernel_iff
    (gammaGroundUnmeasuredTensorCompletionEquiv (M := M) (hc := hc) (B := B))
    (gammaGroundUnmeasuredCoefficientPair (M := M) (hc := hc) (B := B)) H

def gammaGroundUnmeasuredGroupTensorDescend
    (H : GammaGroundUnmeasuredGroupTensor (M := M) hc B →+* V)
    (hH : ∀ a b, gammaGroundUnmeasuredCoefficientPair a b →
      H (gammaGroundUnmeasuredTensorCompletionEquiv (of a)) =
        H (gammaGroundUnmeasuredTensorCompletionEquiv (of b))) :
    GammaGroundRVGrothendieckRing (M := M) hc B →+* V :=
  ringPresentationDescend gammaGroundUnmeasuredGroupTensorMap
    (gammaGroundUnmeasuredGroupTensorMap_surjective hκ hs h00 hsmall hγsmall hΓ)
    gammaGroundUnmeasuredTensorRelationIdeal (gammaGroundUnmeasuredGroupTensor_kernel hκ hs h00 hsmall hγsmall hΓ) H
    ((transportedRelationIdeal_le_kernel_iff gammaGroundUnmeasuredTensorCompletionEquiv
      gammaGroundUnmeasuredCoefficientPair H).mpr hH)

@[simp] theorem gammaGroundUnmeasuredGroupTensorDescend_image
    (H : GammaGroundUnmeasuredGroupTensor (M := M) hc B →+* V)
    (hH : ∀ a b, gammaGroundUnmeasuredCoefficientPair a b →
      H (gammaGroundUnmeasuredTensorCompletionEquiv (of a)) =
        H (gammaGroundUnmeasuredTensorCompletionEquiv (of b)))
    (a : GammaGroundUnmeasuredGroupTensor (M := M) hc B) :
    gammaGroundUnmeasuredGroupTensorDescend hκ hs h00 hsmall hγsmall hΓ H hH
      (gammaGroundUnmeasuredGroupTensorMap a) = H a :=
  ringPresentationDescend_image _ _ _ _ _ _ a

theorem gammaGroundUnmeasuredGroupTensorDescend_unique
    (H : GammaGroundUnmeasuredGroupTensor (M := M) hc B →+* V)
    (hH : ∀ a b, gammaGroundUnmeasuredCoefficientPair a b →
      H (gammaGroundUnmeasuredTensorCompletionEquiv (of a)) =
        H (gammaGroundUnmeasuredTensorCompletionEquiv (of b)))
    (D : GammaGroundRVGrothendieckRing (M := M) hc B →+* V)
    (hD : D.comp gammaGroundUnmeasuredGroupTensorMap = H) :
    D = gammaGroundUnmeasuredGroupTensorDescend hκ hs h00 hsmall hγsmall hΓ H hH :=
  ringPresentationDescend_unique _ _ _ _ _ _ D hD

def proposition_3_18_unmeasured_ring (C : GammaGroundContext M) :
    GammaGroundUnmeasuredGroupTensor (M := M) hc C.base ⧸
      (gammaGroundUnmeasuredTensorRelationIdeal (M := M) (hc := hc) (B := C.base)) ≃+*
        GammaGroundRVGrothendieckRing (M := M) hc C.base :=
  gammaGroundUnmeasuredGroupTensorQuotientEquiv C.uncountable.le C.saturated C.model00
    C.small_real C.small_gamma C.nontrivial_definable_gamma

/-- The entire ring kernel is killed exactly when the explicit positive
translation pairs have equal evaluations. -/
theorem gammaGroundMeasuredGroupTensor_descends_iff
    (H : GammaGroundMeasuredGroupTensor (M := M) hc B →+* V) :
    (∃ D : GammaGroundMeasuredRVGrothendieckRing (M := M) hc B →+* V,
      D.comp gammaGroundMeasuredGroupTensorMap = H) ↔
    ∀ a b, gammaGroundMeasuredCoefficientPair a b →
      H (gammaGroundMeasuredTensorCompletionEquiv (of a)) =
        H (gammaGroundMeasuredTensorCompletionEquiv (of b)) := by
  rw [ringPresentation_descends_iff (gammaGroundMeasuredGroupTensorMap (M := M) (hc := hc) (ground := B))
    (gammaGroundMeasuredGroupTensorMap_surjective hκ hs h00 hsmall hγsmall hΓ)
    (gammaGroundMeasuredTensorRelationIdeal (M := M) (hc := hc) (B := B))
    (gammaGroundMeasuredGroupTensor_kernel hκ hs h00 hsmall hγsmall hΓ) H]
  exact transportedRelationIdeal_le_kernel_iff
    (gammaGroundMeasuredTensorCompletionEquiv (M := M) (hc := hc) (B := B))
    (gammaGroundMeasuredCoefficientPair (M := M) (hc := hc) (B := B)) H

def gammaGroundMeasuredGroupTensorDescend
    (H : GammaGroundMeasuredGroupTensor (M := M) hc B →+* V)
    (hH : ∀ a b, gammaGroundMeasuredCoefficientPair a b →
      H (gammaGroundMeasuredTensorCompletionEquiv (of a)) =
        H (gammaGroundMeasuredTensorCompletionEquiv (of b))) :
    GammaGroundMeasuredRVGrothendieckRing (M := M) hc B →+* V :=
  ringPresentationDescend gammaGroundMeasuredGroupTensorMap
    (gammaGroundMeasuredGroupTensorMap_surjective hκ hs h00 hsmall hγsmall hΓ)
    gammaGroundMeasuredTensorRelationIdeal (gammaGroundMeasuredGroupTensor_kernel hκ hs h00 hsmall hγsmall hΓ) H
    ((transportedRelationIdeal_le_kernel_iff gammaGroundMeasuredTensorCompletionEquiv
      gammaGroundMeasuredCoefficientPair H).mpr hH)

@[simp] theorem gammaGroundMeasuredGroupTensorDescend_image
    (H : GammaGroundMeasuredGroupTensor (M := M) hc B →+* V)
    (hH : ∀ a b, gammaGroundMeasuredCoefficientPair a b →
      H (gammaGroundMeasuredTensorCompletionEquiv (of a)) =
        H (gammaGroundMeasuredTensorCompletionEquiv (of b)))
    (a : GammaGroundMeasuredGroupTensor (M := M) hc B) :
    gammaGroundMeasuredGroupTensorDescend hκ hs h00 hsmall hγsmall hΓ H hH
      (gammaGroundMeasuredGroupTensorMap a) = H a :=
  ringPresentationDescend_image _ _ _ _ _ _ a

theorem gammaGroundMeasuredGroupTensorDescend_unique
    (H : GammaGroundMeasuredGroupTensor (M := M) hc B →+* V)
    (hH : ∀ a b, gammaGroundMeasuredCoefficientPair a b →
      H (gammaGroundMeasuredTensorCompletionEquiv (of a)) =
        H (gammaGroundMeasuredTensorCompletionEquiv (of b)))
    (D : GammaGroundMeasuredRVGrothendieckRing (M := M) hc B →+* V)
    (hD : D.comp gammaGroundMeasuredGroupTensorMap = H) :
    D = gammaGroundMeasuredGroupTensorDescend hκ hs h00 hsmall hγsmall hΓ H hH :=
  ringPresentationDescend_unique _ _ _ _ _ _ D hD

def proposition_3_18_measured_ring (C : GammaGroundContext M) :
    GammaGroundMeasuredGroupTensor (M := M) hc C.base ⧸
      (gammaGroundMeasuredTensorRelationIdeal (M := M) (hc := hc) (B := C.base)) ≃+*
        GammaGroundMeasuredRVGrothendieckRing (M := M) hc C.base :=
  gammaGroundMeasuredGroupTensorQuotientEquiv C.uncountable.le C.saturated C.model00
    C.small_real C.small_gamma C.nontrivial_definable_gamma

/-- The full annular pullback lands in the displayed ideal of coefficient
translation differences, including the ambiguity of the presentation. -/
theorem gammaGroundAnnularPullback_le_tensor_relation_ideal
    {T : Type} [CommRing T]
    (q : T →+* GammaGroundMeasuredRVGrothendieckRing (M := M) hc B)
    (f : T →+* GammaGroundUnmeasuredGroupTensor (M := M) hc B)
    (hcomm : gammaGroundUnmeasuredGroupTensorMap.comp f = gammaGroundMeasuredRVForgetRing.comp q) :
    Ideal.comap q (gammaGroundAnnularIdeal (M := M) (hc := hc) (B := B)) ≤
      Ideal.comap f (gammaGroundUnmeasuredTensorRelationIdeal (M := M) (hc := hc) (B := B)) := by
  rw [← gammaGroundUnmeasuredGroupTensor_kernel hκ hs h00 hsmall hγsmall hΓ]
  exact gammaGroundAnnularPullback_le_actual_tensor_kernel q f hcomm

end DiamondIntegral.Section3
