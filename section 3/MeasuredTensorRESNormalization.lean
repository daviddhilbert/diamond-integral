import «section 3».MeasuredRESWeightPartitions
import «section 3».MeasuredTensorObjectNormalForm
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {r n : ℕ}

def GammaGroundMeasuredRESObject.normalizeCombinedWeight (X : GammaGroundMeasuredRESObject hc B r) :
    GammaGroundMeasuredRESObject hc B r :=
  (show GammaGroundRESObject hc B r from ⟨X.obj.underlying,X.property⟩).withCombinedWeight
    (gammaGroundOneForm X.obj.underlying.domain)

@[simp] theorem GammaGroundMeasuredRESObject.normalizeCombinedWeight_value (X : GammaGroundMeasuredRESObject hc B r)
    (a : X.obj.underlying.domain) : X.normalizeCombinedWeight.obj.combinedWeight a = 1 :=
  (X.obj.underlying.withCombinedWeight_value _ a).trans (gammaGroundOneForm_value _ a)

theorem gammaGroundMeasuredTensor_constant_RES_normalization
    (X : GammaGroundMeasuredRESObject hc B r) (A : GammaGroundMeasuredGammaObject hc B n)
    (δ : Values.Gamma (M := M)) (hδ : GammaDefinableClosureAtBase B δ)
    (hX : ∀ a, X.obj.combinedWeight a = δ) :
    gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass A =
    gammaGroundMeasuredRESDirectSumClass X.normalizeCombinedWeight ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
      gammaGroundMeasuredGammaSemiringClass (A.shiftCombinedWeight δ hδ) := by
  let Y := X.normalizeCombinedWeight
  let f : GammaGroundMeasuredRVHom (Y.shiftCombinedWeight δ hδ).obj X.obj :=
    { bijection := GammaGroundBijection.id X.obj.underlying.domain
      preserves := by
        intro a
        rw [Y.shiftCombinedWeight_value]
        have hy : Y.obj.combinedWeight a = 1 := X.normalizeCombinedWeight_value a
        rw [hy,one_mul]
        exact (hX a).symm }
  have he := gammaGroundMeasuredRESClass_iso (gammaGroundMeasuredResProperty.isoMk
    (asIso (show (Y.shiftCombinedWeight δ hδ).obj ⟶ X.obj from f)))
  have hclass : gammaGroundMeasuredRESDirectSumClass (Y.shiftCombinedWeight δ hδ) =
      gammaGroundMeasuredRESDirectSumClass X := congrArg (DirectSum.of (GammaGroundMeasuredRESKPlus hc B) r) he
  rw [← hclass]
  exact gammaGroundMeasuredTensor_shared_weight_shift Y A δ hδ

/-- Every measured pure tensor is a finite positive sum whose RES
combined weights are one. All original degrees are preserved. -/
theorem gammaGroundMeasuredTensor_RES_weight_normalization {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hγsmall : Cardinal.mk B.gamma < κ)
    (X : GammaGroundMeasuredRESObject hc B r) (A : GammaGroundMeasuredGammaObject hc B n) :
    ∃ N : ℕ, ∃ Y : Fin N → GammaGroundMeasuredRESObject hc B r,
      ∃ H : Fin N → GammaGroundMeasuredGammaObject hc B n,
      (∀ i a, (Y i).obj.combinedWeight a = 1) ∧
      gammaGroundMeasuredRESDirectSumClass X ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
        gammaGroundMeasuredGammaSemiringClass A =
          ∑ i, gammaGroundMeasuredRESDirectSumClass (Y i) ⊗ₜ[GammaGroundMeasuredFiniteGammaPositiveSemiring hc B]
            gammaGroundMeasuredGammaSemiringClass (H i) := by
  obtain ⟨N,δ,Q,hδ,hQ,hd,hcov,hw⟩ := gammaGroundMeasuredRES_constant_weight_partition
    hκ hs h00 hsmall hγsmall X
  let Z := fun i => X.restrict (Q i) (hQ i)
  let Y := fun i => (Z i).normalizeCombinedWeight
  let H := fun i => A.shiftCombinedWeight (δ i) (hδ i)
  refine ⟨N,Y,H,fun i a => (Z i).normalizeCombinedWeight_value a,?_⟩
  have hp : gammaGroundMeasuredRESDirectSumClass X = ∑ i, gammaGroundMeasuredRESDirectSumClass (Z i) := by
    have hp := gammaGroundMeasuredRESDirectSumClass_finite_partition X Q hd hcov
    exact hp
  rw [hp,TensorProduct.sum_tmul]
  apply Finset.sum_congr rfl
  intro i _
  apply gammaGroundMeasuredTensor_constant_RES_normalization (Z i) A (δ i) (hδ i)
  intro a
  exact hw i ⟨a.val,hQ i a.property⟩ a.property
end DiamondIntegral.Section3
