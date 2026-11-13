import «section 4».GammaOrdinaryBoundedComparison
import «section 4».RVOrdinaryTensorEvaluation

/-! The actual bounded-to-full map between the finite-Gamma-balanced
tensor sources is graded. Its RV comparison square commutes, and the
ordinary full evaluation restricts to the constructed bounded evaluation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVBoundedTensorComparison
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gammaForget (B : Base (M := M)) : GammaBoundedRVPresentation.ChartRing B →ₐ[GammaFiniteRVPresentation.ChartRing B]
    GammaRVChartPresentation.ChartRing B where
  toRingHom := GammaBoundedRVMaps.forget B
  commutes' c := RingHom.congr_fun (GammaFiniteRVMaps.forget_bounded B) c

def toFull (B : Base (M := M)) : RVBoundedBalancedTensor.Source B →ₐ[GammaFiniteRVPresentation.ChartRing B]
    RVFiniteBalancedTensor.Source B :=
  Algebra.TensorProduct.map (AlgHom.id (GammaFiniteRVPresentation.ChartRing B) (RESChartRing.Ring B)) (gammaForget B)

theorem toFull_tmul (B : Base (M := M)) (x : RESChartRing.Ring B) (y : GammaBoundedRVPresentation.ChartRing B) :
    toFull B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) = x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] GammaBoundedRVMaps.forget B y := rfl

def rvForget (B : Base (M := M)) : RVBoundedRing.Ring B →ₐ[GammaFiniteRVPresentation.ChartRing B] RVChartRing.Ring B where
  toRingHom := RVBoundedMaps.forget B
  commutes' c := RingHom.congr_fun (RVBoundedMaps.forget_ofRES B) (GammaFiniteRVMaps.sharp B c)

theorem comparison_square (B : Base (M := M)) :
    (RVFiniteBalancedTensor.comparison B).comp (toFull B) = (rvForget B).comp (RVBoundedBalancedTensor.comparison B) := by
  apply Algebra.TensorProduct.ext'
  intro x y
  change RVFiniteBalancedTensor.comparison B (toFull B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y)) = _
  rw [toFull_tmul, RVFiniteBalancedTensor.comparison_tmul]
  change _ = RVBoundedMaps.forget B (RVBoundedBalancedTensor.comparison B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y))
  rw [RVBoundedBalancedTensor.comparison_tmul, map_mul]
  exact (congrArg₂ (· * ·) (RingHom.congr_fun (RVBoundedMaps.forget_ofRES B) x)
    (RingHom.congr_fun (GammaBoundedRVMaps.forget_sharp B) y)).symm

def gradedToFull (B : Base (M := M)) :
    GradedRingHom (RVBalancedGradings.boundedPiece B) (RVBalancedGradings.measuredPiece B) :=
  TensorGradedMaps.gradedMap (RVBalancedGradings.boundedData B) (RVBalancedGradings.measuredCoaction B) (toFull B).toRingHom (by
    intro m n x y hx hy
    change toFull B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) ∈ RVBalancedGradings.measuredPiece B (m + n)
    rw [toFull_tmul]
    exact RVBalancedGradings.measured_tmul_mem B hx ((GammaBoundedRVProfiles.gradedForget B).map_mem hy))

theorem evaluation_square (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k).comp (toFull B) =
      RVBoundedBalancedTensor.evaluation hc h00 linear hκ hs B hr hγ hΓ k := by
  apply Algebra.TensorProduct.ext'
  intro x y
  change RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k (toFull B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y)) = _
  rw [toFull_tmul, RVOrdinaryTensorEvaluation.evaluation_tmul, RVBoundedBalancedTensor.evaluation_tmul]
  exact congrArg (RESOrdinaryReduction.forget B x * ·)
    (RingHom.congr_fun (GammaOrdinaryBoundedComparison.evaluation_forget hc h00 linear hκ hs B hr hγ hΓ k) y)

theorem evaluation_independent_on_bounded (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k l : EulerKind) :
    (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k).comp (toFull B) =
      (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ l).comp (toFull B) :=
  (evaluation_square hc h00 linear hκ hs B hr hγ hΓ k).trans
    ((RVBoundedBalancedTensor.evaluation_independent_kind hc h00 linear hκ hs B hr hγ hΓ k l).trans
      (evaluation_square hc h00 linear hκ hs B hr hγ hΓ l).symm)

end DiamondIntegral.Section4.RVBoundedTensorComparison
