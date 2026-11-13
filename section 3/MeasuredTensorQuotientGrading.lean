import «section 3».MeasuredTensorPositiveKernel
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
def gammaGroundMeasuredCoefficientQuotientEquivDirectSum {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) :
    GammaGroundMeasuredCoefficientQuotient hc B ≃+* GammaGroundMeasuredRVDirectSum hc B :=
  (gammaGroundMeasuredCoefficientQuotientEquiv hκ hs h00 hsmall hγsmall hΓ).trans
    gammaGroundMeasuredRVSemiringEquivDirectSum

/-- The grading on pure object tensors is their original sum of label
degrees, rather than an arity chosen during the geometric proof. -/
theorem gammaGroundMeasuredCoefficientQuotientEquivDirectSum_objects {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {r n : ℕ}
    (X : GammaGroundMeasuredRESObject hc B r) (G : GammaGroundMeasuredGammaObject hc B n) :
    gammaGroundMeasuredCoefficientQuotientEquivDirectSum hκ hs h00 hsmall hγsmall hΓ
      ((gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B)).mk'
        (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
          gammaGroundMeasuredGammaSemiringClass G)) =
      DirectSum.of (GammaGroundMeasuredRVKPlus hc B) (r+n) (gammaGroundMeasuredRVClass (X.obj.product G.rvLift)) := by
  change gammaGroundMeasuredRVPresentationToDirectSum
    (gammaGroundMeasuredTensorMap (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass G)) = _
  rw [gammaGroundMeasuredTensorMap_objects,gammaGroundMeasuredRVPresentationToDirectSum_class]
  rfl

def gammaGroundMeasuredCoefficientQuotientDegreeInclusion {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : ℕ) :
    GammaGroundMeasuredRVKPlus hc B k →+ GammaGroundMeasuredCoefficientQuotient hc B where
  toFun a := (gammaGroundMeasuredCoefficientQuotientEquivDirectSum hκ hs h00 hsmall hγsmall hΓ).symm
    (DirectSum.of (GammaGroundMeasuredRVKPlus hc B) k a)
  map_zero' := by rw [map_zero,map_zero]
  map_add' a b := by rw [map_add,map_add]

@[simp] theorem gammaGroundMeasuredCoefficientQuotientDegreeInclusion_image {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : ℕ) (a : GammaGroundMeasuredRVKPlus hc B k) :
    gammaGroundMeasuredCoefficientQuotientEquivDirectSum hκ hs h00 hsmall hγsmall hΓ
      (gammaGroundMeasuredCoefficientQuotientDegreeInclusion hκ hs h00 hsmall hγsmall hΓ k a) =
      DirectSum.of (GammaGroundMeasuredRVKPlus hc B) k a :=
  (gammaGroundMeasuredCoefficientQuotientEquivDirectSum hκ hs h00 hsmall hγsmall hΓ).apply_symm_apply _

theorem gammaGroundMeasuredCoefficientQuotient_objects_in_degree {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) {r n : ℕ}
    (X : GammaGroundMeasuredRESObject hc B r) (G : GammaGroundMeasuredGammaObject hc B n) :
    (gammaGroundMeasuredCoefficientCongruence (hc := hc) (B := B)).mk'
      (gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass G) =
      gammaGroundMeasuredCoefficientQuotientDegreeInclusion hκ hs h00 hsmall hγsmall hΓ (r+n)
        (gammaGroundMeasuredRVClass (X.obj.product G.rvLift)) := by
  apply (gammaGroundMeasuredCoefficientQuotientEquivDirectSum hκ hs h00 hsmall hγsmall hΓ).injective
  rw [gammaGroundMeasuredCoefficientQuotientEquivDirectSum_objects,
    gammaGroundMeasuredCoefficientQuotientDegreeInclusion_image]
end DiamondIntegral.Section3
