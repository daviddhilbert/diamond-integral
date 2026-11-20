import «section 4».RVT001NormalizedDistinct

/-! The normalized geometric and bounded maps differ by a power of the affine
class on classes where the two evaluations agree (for Remark 7.28,
`eg:eb:factor`).

The geometric normalization sends a degree-`n` value `y` to `y·[A]^{-n}` in the
affine localization, and the bounded normalization sends it to `y`
(`RESAffineNormalization.comparison_homogeneous`). So if a degree-`n` ordinary RV
class has equal geometric and bounded evaluations, then
`E_g(x) = E_b(x)·[A]^{-n}` (`geometric_eq_bounded_mul`). The agreement of the two
evaluations on doubly bounded classes is the content of Remark 7.28; it is
supplied separately. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVT001BoundedFactor

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (p : ApprovedT001Presentation.Ordinary B)

/-- In the affine localization, `y / [A]^n = y · [A]^{-n}`. -/
theorem mk_pow_eq (y : RESDimensionFreeReduction.Ring B) (n : ℕ) :
    (Localization.mk y (⟨RESAffineLocalization.dimensionFreeAffine B ^ n, ⟨n, rfl⟩⟩ :
        Submonoid.powers (RESAffineLocalization.dimensionFreeAffine B)) : RESAffineLocalization.Target B) =
      algebraMap _ (RESAffineLocalization.Target B) y *
        IsLocalization.Away.invSelf (RESAffineLocalization.dimensionFreeAffine B) ^ n := by
  rw [Localization.mk_eq_mk', IsLocalization.Away.invSelf, ← IsLocalization.mk'_pow, one_pow,
    IsLocalization.mk'_eq_mul_mk'_one]
  congr 2

/-- If a degree-`n` ordinary RV class has equal geometric and bounded
evaluations, its normalized geometric value is its bounded value times
`[A]^{-n}`. -/
theorem geometric_eq_bounded_mul (n : ℕ) (x : RVOrdinaryRing.Ring B)
    (hx : x ∈ RVOrdinaryGrading.gradedPiece B n)
    (he : RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p .geometric x =
      RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p .bounded x) :
    RVT001OrdinaryNormalization.geometric h00 linear hκ hs B hr hγ hΓ p (RVOrdinaryPNormalization.quotient B x) =
      RVT001NormalizedDistinct.boundedInAffine h00 linear hκ hs B hr hγ hΓ p (RVOrdinaryPNormalization.quotient B x) *
        IsLocalization.Away.invSelf (RESAffineLocalization.dimensionFreeAffine B) ^ n := by
  have hy : RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p .geometric x ∈
      RESReductionGradings.ordinaryPiece B n :=
    (RVT001OrdinaryDescent.gradedEvaluation h00 linear hκ hs B hr hγ hΓ p .geometric).map_mem hx
  change RESAffineLocalization.comparison B (RESAffineNormalization.normalize B
      (RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p .geometric x)) =
    algebraMap _ (RESAffineLocalization.Target B) (RESDimensionFreeReduction.fromGradedReduced B
      (RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p .bounded x)) * _
  rw [RESAffineNormalization.comparison_homogeneous B hy, he, mk_pow_eq]

end DiamondIntegral.Section4.RVT001BoundedFactor
