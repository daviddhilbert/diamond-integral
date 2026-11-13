import «section 3».TensorPresentationContext
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}
variable {R : Type} [CommSemiring R]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
variable (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B)
include hκ hs h00 hsmall hγsmall hΓ

/-- Descent uses the proved positive kernel presentation, with a
semiring target. It requires no cancellation or groupification. -/
def gammaGroundUnmeasuredTensorDescend (H : GammaGroundUnmeasuredPositiveTensor hc B →+* R)
    (hH : ∀ a b, gammaGroundUnmeasuredCoefficientPair a b → H a = H b) :
    GammaGroundRVPositiveSemiring hc B →+* R :=
  ((gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B)).lift H
    (RingCon.ringConGen_le.mpr hH)).comp
      (gammaGroundUnmeasuredCoefficientQuotientEquiv hκ hs h00 hsmall hγsmall hΓ).symm.toRingHom

@[simp] theorem gammaGroundUnmeasuredTensorDescend_image
    (H : GammaGroundUnmeasuredPositiveTensor hc B →+* R)
    (hH : ∀ a b, gammaGroundUnmeasuredCoefficientPair a b → H a = H b)
    (a : GammaGroundUnmeasuredPositiveTensor hc B) :
    gammaGroundUnmeasuredTensorDescend hκ hs h00 hsmall hγsmall hΓ H hH
      (gammaGroundUnmeasuredTensorMap a) = H a := by
  let E := gammaGroundUnmeasuredCoefficientQuotientEquiv (hc := hc) (B := B) hκ hs h00 hsmall hγsmall hΓ
  change ((gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B)).lift H
    (RingCon.ringConGen_le.mpr hH)) (E.symm (gammaGroundUnmeasuredTensorMap a)) = H a
  have he : E ((gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B)).mk' a) =
      gammaGroundUnmeasuredTensorMap a := rfl
  rw [← he,E.symm_apply_apply]
  rfl

theorem gammaGroundUnmeasuredTensorDescend_unique
    (H : GammaGroundUnmeasuredPositiveTensor hc B →+* R)
    (hH : ∀ a b, gammaGroundUnmeasuredCoefficientPair a b → H a = H b)
    (F : GammaGroundRVPositiveSemiring hc B →+* R)
    (hF : F.comp gammaGroundUnmeasuredTensorMap = H) :
    F = gammaGroundUnmeasuredTensorDescend hκ hs h00 hsmall hγsmall hΓ H hH := by
  apply RingHom.ext
  intro v
  obtain ⟨a,rfl⟩ := gammaGroundUnmeasuredTensorMap_surjective (hc := hc) hκ hs h00 hsmall hγsmall hΓ v
  exact (RingHom.congr_fun hF a).trans
    (gammaGroundUnmeasuredTensorDescend_image hκ hs h00 hsmall hγsmall hΓ H hH a).symm

/-- Testing only the explicit elementary pairs is necessary and
sufficient for an arbitrary positive tensor evaluation to descend. -/
theorem gammaGroundUnmeasuredTensor_descends_iff
    (H : GammaGroundUnmeasuredPositiveTensor hc B →+* R) :
    (∃ F : GammaGroundRVPositiveSemiring hc B →+* R, F.comp gammaGroundUnmeasuredTensorMap = H) ↔
      ∀ a b, gammaGroundUnmeasuredCoefficientPair a b → H a = H b := by
  constructor
  · rintro ⟨F,hF⟩ a b hab
    have h := congrArg F (gammaGroundUnmeasuredCoefficientPair_valid hab)
    exact (RingHom.congr_fun hF a).symm.trans (h.trans (RingHom.congr_fun hF b))
  · intro hH
    refine ⟨gammaGroundUnmeasuredTensorDescend hκ hs h00 hsmall hγsmall hΓ H hH,?_⟩
    exact RingHom.ext (gammaGroundUnmeasuredTensorDescend_image hκ hs h00 hsmall hγsmall hΓ H hH)

def gammaGroundMeasuredTensorDescend (H : GammaGroundMeasuredPositiveTensor hc B →+* R)
    (hH : ∀ a b, gammaGroundMeasuredCoefficientPair a b → H a = H b) :
    GammaGroundMeasuredRVPositiveSemiring hc B →+* R :=
  ((gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B)).lift H
    (RingCon.ringConGen_le.mpr hH)).comp
      (gammaGroundMeasuredCoefficientQuotientEquiv hκ hs h00 hsmall hγsmall hΓ).symm.toRingHom

@[simp] theorem gammaGroundMeasuredTensorDescend_image
    (H : GammaGroundMeasuredPositiveTensor hc B →+* R)
    (hH : ∀ a b, gammaGroundMeasuredCoefficientPair a b → H a = H b)
    (a : GammaGroundMeasuredPositiveTensor hc B) :
    gammaGroundMeasuredTensorDescend hκ hs h00 hsmall hγsmall hΓ H hH
      (gammaGroundMeasuredTensorMap a) = H a := by
  let E := gammaGroundMeasuredCoefficientQuotientEquiv (hc := hc) (B := B) hκ hs h00 hsmall hγsmall hΓ
  change ((gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B)).lift H
    (RingCon.ringConGen_le.mpr hH)) (E.symm (gammaGroundMeasuredTensorMap a)) = H a
  have he : E ((gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B)).mk' a) =
      gammaGroundMeasuredTensorMap a := rfl
  rw [← he,E.symm_apply_apply]
  rfl

theorem gammaGroundMeasuredTensorDescend_unique
    (H : GammaGroundMeasuredPositiveTensor hc B →+* R)
    (hH : ∀ a b, gammaGroundMeasuredCoefficientPair a b → H a = H b)
    (F : GammaGroundMeasuredRVPositiveSemiring hc B →+* R)
    (hF : F.comp gammaGroundMeasuredTensorMap = H) :
    F = gammaGroundMeasuredTensorDescend hκ hs h00 hsmall hγsmall hΓ H hH := by
  apply RingHom.ext
  intro v
  obtain ⟨a,rfl⟩ := gammaGroundMeasuredTensorMap_surjective (hc := hc) hκ hs h00 hsmall hγsmall hΓ v
  exact (RingHom.congr_fun hF a).trans
    (gammaGroundMeasuredTensorDescend_image hκ hs h00 hsmall hγsmall hΓ H hH a).symm

theorem gammaGroundMeasuredTensor_descends_iff
    (H : GammaGroundMeasuredPositiveTensor hc B →+* R) :
    (∃ F : GammaGroundMeasuredRVPositiveSemiring hc B →+* R, F.comp gammaGroundMeasuredTensorMap = H) ↔
      ∀ a b, gammaGroundMeasuredCoefficientPair a b → H a = H b := by
  constructor
  · rintro ⟨F,hF⟩ a b hab
    have h := congrArg F (gammaGroundMeasuredCoefficientPair_valid hab)
    exact (RingHom.congr_fun hF a).symm.trans (h.trans (RingHom.congr_fun hF b))
  · intro hH
    refine ⟨gammaGroundMeasuredTensorDescend hκ hs h00 hsmall hγsmall hΓ H hH,?_⟩
    exact RingHom.ext (gammaGroundMeasuredTensorDescend_image hκ hs h00 hsmall hγsmall hΓ H hH)
end DiamondIntegral.Section3
