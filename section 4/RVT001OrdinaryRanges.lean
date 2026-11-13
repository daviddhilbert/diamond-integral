import «section 4».RVT001OrdinaryNormalization
import «section 4».RESOrdinarySurjectivity

/-! Exact ranges after T001 descent. The graded ordinary Euler maps are
onto the reduced RES ring; their point and homogeneous affine
normalizations are onto the intended targets. The subsequent geometric
comparison has exactly the range of the natural localization comparison,
without a surjectivity or injectivity assertion about that comparison. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVT001OrdinaryRanges
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem dimensionFree_surjective (B : Base (M := M)) :
    Function.Surjective (RESDimensionFreeReduction.fromGradedReduced B) :=
  (RESDimensionFreeReduction.normalizationEquiv B).surjective.comp Ideal.Quotient.mk_surjective

theorem affine_surjective (B : Base (M := M)) : Function.Surjective (RESAffineNormalization.normalize B) := by
  intro y
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective ((RESAffineNormalization.equivalence B).symm y)
  refine ⟨x, ?_⟩
  have he := congrArg (RESAffineNormalization.equivalence B) hx
  change RESAffineNormalization.normalize B x =
    (RESAffineNormalization.equivalence B) ((RESAffineNormalization.equivalence B).symm y) at he
  exact he.trans ((RESAffineNormalization.equivalence B).apply_symm_apply y)

variable (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M))
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
variable (hΓ : Section2.NontrivialDefinableGamma B) (p : ApprovedT001Presentation.Ordinary B)

theorem evaluation_surjective (kind : EulerKind) :
    Function.Surjective (RVT001OrdinaryDescent.evaluation h00 linear hκ hs B hr hγ hΓ p kind) := by
  intro y
  obtain ⟨x, hx⟩ := RVOrdinaryBalancedSpecialClasses.evaluation_surjective h00 linear hκ hs B hr hγ hΓ kind y
  exact ⟨RVOrdinaryBalancedTensor.comparison B x,
    (RVT001OrdinaryDescent.evaluation_comparison h00 linear hκ hs B hr hγ hΓ p kind x).trans hx⟩

theorem boundedEvaluation_surjective (kind : EulerKind) :
    Function.Surjective (RVT001OrdinaryDescent.boundedEvaluation h00 linear hκ hs B hr hγ hΓ p kind) := by
  intro y
  obtain ⟨x, hx⟩ := RESOrdinarySurjectivity.reducedForget_surjective B y
  exact ⟨RVBoundedMaps.ofRES B x, (RVT001OrdinaryDescent.boundedEvaluation_res h00 linear hκ hs B hr hγ hΓ p kind x).trans hx⟩

theorem radiusEvaluation_surjective (kind : EulerKind) :
    Function.Surjective (RVT001OrdinaryDescent.radiusEvaluation h00 linear hκ hs B hr hγ hΓ p kind) := by
  intro y
  obtain ⟨x, hx⟩ := RESOrdinarySurjectivity.reducedForget_surjective B y
  exact ⟨RVRadiusQuotient.ofRES B x, (RVT001OrdinaryDescent.radiusEvaluation_res h00 linear hκ hs B hr hγ hΓ p kind x).trans hx⟩

theorem boundedRaw_surjective :
    Function.Surjective (RVT001OrdinaryNormalization.boundedRaw h00 linear hκ hs B hr hγ hΓ p) :=
  (dimensionFree_surjective B).comp (evaluation_surjective h00 linear hκ hs B hr hγ hΓ p EulerKind.bounded)

theorem homogeneousRaw_surjective :
    Function.Surjective (RVT001OrdinaryNormalization.homogeneousRaw h00 linear hκ hs B hr hγ hΓ p) :=
  (affine_surjective B).comp (evaluation_surjective h00 linear hκ hs B hr hγ hΓ p EulerKind.geometric)

theorem bounded_surjective :
    Function.Surjective (RVT001OrdinaryNormalization.bounded h00 linear hκ hs B hr hγ hΓ p) := by
  intro y
  obtain ⟨x, hx⟩ := boundedRaw_surjective h00 linear hκ hs B hr hγ hΓ p y
  exact ⟨RVOrdinaryPNormalization.quotient B x, hx⟩

theorem homogeneous_surjective :
    Function.Surjective (RVT001OrdinaryNormalization.homogeneous h00 linear hκ hs B hr hγ hΓ p) := by
  intro y
  obtain ⟨x, hx⟩ := homogeneousRaw_surjective h00 linear hκ hs B hr hγ hΓ p y
  exact ⟨RVOrdinaryPNormalization.quotient B x, hx⟩

theorem geometric_range :
    Set.range (RVT001OrdinaryNormalization.geometric h00 linear hκ hs B hr hγ hΓ p) =
      Set.range (RESAffineLocalization.comparison B) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨RVT001OrdinaryNormalization.homogeneous h00 linear hκ hs B hr hγ hΓ p x, rfl⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨x, hx⟩ := homogeneous_surjective h00 linear hκ hs B hr hγ hΓ p z
    exact ⟨x, congrArg (RESAffineLocalization.comparison B) hx⟩

end DiamondIntegral.Section4.RVT001OrdinaryRanges
