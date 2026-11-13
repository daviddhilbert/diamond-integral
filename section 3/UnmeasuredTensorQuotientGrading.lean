import «section 3».UnmeasuredTensorPositiveKernel
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)}

/-- The positive quotient has the actual fixed-degree RV direct-sum
grading. This equivalence respects both addition and multiplication. -/
def gammaGroundUnmeasuredCoefficientQuotientEquivDirectSum {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    GammaGroundUnmeasuredCoefficientQuotient hc B ≃+* GammaGroundRVDirectSum hc B :=
  (gammaGroundUnmeasuredCoefficientQuotientEquiv hκ hs h00 hsmall hγsmall hΓ).trans
    gammaGroundRVSemiringEquivDirectSum

/-- The grading on pure object tensors is their original sum of label
degrees, rather than an arity chosen during the geometric proof. -/
theorem gammaGroundUnmeasuredCoefficientQuotientEquivDirectSum_objects {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {r n : ℕ}
    (X : GammaGroundRESObject hc B r) (G : GammaGroundGammaObject hc B n) :
    gammaGroundUnmeasuredCoefficientQuotientEquivDirectSum hκ hs h00 hsmall hγsmall hΓ
      ((gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B)).mk'
        (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
          gammaGroundGammaSemiringClass G)) =
      DirectSum.of (GammaGroundRVKPlus hc B) (r+n) (gammaGroundRVClass (X.obj.product G.rvLift)) := by
  change gammaGroundRVPresentationToDirectSum
    (gammaGroundUnmeasuredTensorMap (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
      gammaGroundGammaSemiringClass G)) = _
  rw [gammaGroundUnmeasuredTensorMap_objects,gammaGroundRVPresentationToDirectSum_class]
  rfl

def gammaGroundUnmeasuredCoefficientQuotientDegreeInclusion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : ℕ) :
    GammaGroundRVKPlus hc B k →+ GammaGroundUnmeasuredCoefficientQuotient hc B where
  toFun a := (gammaGroundUnmeasuredCoefficientQuotientEquivDirectSum hκ hs h00 hsmall hγsmall hΓ).symm
    (DirectSum.of (GammaGroundRVKPlus hc B) k a)
  map_zero' := by rw [map_zero,map_zero]
  map_add' a b := by rw [map_add,map_add]

@[simp] theorem gammaGroundUnmeasuredCoefficientQuotientDegreeInclusion_image {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : ℕ) (a : GammaGroundRVKPlus hc B k) :
    gammaGroundUnmeasuredCoefficientQuotientEquivDirectSum hκ hs h00 hsmall hγsmall hΓ
      (gammaGroundUnmeasuredCoefficientQuotientDegreeInclusion hκ hs h00 hsmall hγsmall hΓ k a) =
      DirectSum.of (GammaGroundRVKPlus hc B) k a :=
  (gammaGroundUnmeasuredCoefficientQuotientEquivDirectSum hκ hs h00 hsmall hγsmall hΓ).apply_symm_apply _

theorem gammaGroundUnmeasuredCoefficientQuotient_objects_in_degree {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {r n : ℕ}
    (X : GammaGroundRESObject hc B r) (G : GammaGroundGammaObject hc B n) :
    (gammaGroundUnmeasuredCoefficientCongruence (hc := hc) (B := B)).mk'
      (gammaGroundRESDirectSumClass X ⊗ₜ[GammaGroundFiniteGammaPositiveSemiring hc B]
        gammaGroundGammaSemiringClass G) =
      gammaGroundUnmeasuredCoefficientQuotientDegreeInclusion hκ hs h00 hsmall hγsmall hΓ (r+n)
        (gammaGroundRVClass (X.obj.product G.rvLift)) := by
  apply (gammaGroundUnmeasuredCoefficientQuotientEquivDirectSum hκ hs h00 hsmall hγsmall hΓ).injective
  rw [gammaGroundUnmeasuredCoefficientQuotientEquivDirectSum_objects,
    gammaGroundUnmeasuredCoefficientQuotientDegreeInclusion_image]
end DiamondIntegral.Section3
