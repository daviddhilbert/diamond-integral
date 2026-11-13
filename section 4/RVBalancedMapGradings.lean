import «section 4».RVBalancedGradings
import «section 4».TensorGradedMaps

/-! The actual finite-Gamma-balanced comparison and evaluation maps are
graded on their whole tensor sources. Global RV descent remains separate. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVBalancedMapGradings
open RVBalancedGradings
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gradedMeasuredComparison (B : Base (M := M)) :
    GradedRingHom (measuredPiece B) (RVGrading.gradedPiece B) :=
  TensorGradedMaps.gradedMap (measuredData B) (RVGrading.gradingCoaction B) (RVFiniteBalancedTensor.comparison B).toRingHom (by
    intro m n x y hx hy
    change RVFiniteBalancedTensor.comparison B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) ∈ RVGrading.gradedPiece B (m + n)
    rw [RVFiniteBalancedTensor.comparison_tmul]
    exact SetLike.mul_mem_graded (RVChartMaps.ofRES_mem B hx) ((GammaRVMapGradings.gradedSharp B).map_mem hy))

def gradedBoundedComparison (B : Base (M := M)) :
    GradedRingHom (boundedPiece B) (RVBoundedGrading.gradedPiece B) :=
  TensorGradedMaps.gradedMap (boundedData B) (RVBoundedGrading.gradingCoaction B) (RVBoundedBalancedTensor.comparison B).toRingHom (by
    intro m n x y hx hy
    change RVBoundedBalancedTensor.comparison B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) ∈ RVBoundedGrading.gradedPiece B (m + n)
    rw [RVBoundedBalancedTensor.comparison_tmul]
    exact SetLike.mul_mem_graded (RVBoundedMaps.ofRES_mem B hx) ((GammaBoundedRVProfiles.gradedSharp B).map_mem hy))

def gradedMeasuredEvaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GradedRingHom (measuredPiece B) (RESReductionGradings.measuredPiece B) :=
  TensorGradedMaps.gradedMap (measuredData B) (RESReductionGradings.measuredCoaction B)
    (RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom (by
      intro m n x y hx hy
      change RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ k
        (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) ∈ RESReductionGradings.measuredPiece B (m + n)
      rw [RVFiniteBalancedTensor.evaluation_tmul]
      exact SetLike.mul_mem_graded (RESReductionGradings.measured_quotient_mem B hx)
        ((GammaRVMapGradings.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k).map_mem hy))

def gradedBoundedEvaluation (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GradedRingHom (boundedPiece B) (RESReductionGradings.ordinaryPiece B) :=
  TensorGradedMaps.gradedMap (boundedData B) (RESReductionGradings.ordinaryCoaction B)
    (RVBoundedBalancedTensor.evaluation hc h00 linear hκ hs B hr hγ hΓ k).toRingHom (by
      intro m n x y hx hy
      change RVBoundedBalancedTensor.evaluation hc h00 linear hκ hs B hr hγ hΓ k
        (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) ∈ RESReductionGradings.ordinaryPiece B (m + n)
      rw [RVBoundedBalancedTensor.evaluation_tmul]
      exact SetLike.mul_mem_graded (RESReductionGradings.forget_mem B hx)
        ((GammaBoundedRVProfiles.gradedEvaluation hc h00 linear hκ hs B hr hγ hΓ k).map_mem hy))

end DiamondIntegral.Section4.RVBalancedMapGradings
