import «section 4».GammaOrdinaryEvaluation
import «section 4».RVBalancedMapGradings

/-! Both ordinary Euler evaluations are actual graded maps on the full
finite-Gamma-balanced measured tensor. They forget volume on the RES
factor and use chi(I) T^n on Gamma. Global RV descent is separate. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVOrdinaryTensorEvaluation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def gammaEvaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GammaRVChartPresentation.ChartRing B →ₐ[GammaFiniteRVPresentation.ChartRing B] RESOrdinaryReduction.ReducedRing B where
  toRingHom := GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k
  commutes' c := (GammaOrdinaryEvaluation.finite_balance_apply h00 linear hκ hs B hr hγ hΓ k c).symm

def evaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    RVFiniteBalancedTensor.Source B →ₐ[GammaFiniteRVPresentation.ChartRing B] RESOrdinaryReduction.ReducedRing B :=
  Algebra.TensorProduct.lift (RVBoundedBalancedTensor.resEvaluation B)
    (gammaEvaluation h00 linear hκ hs B hr hγ hΓ k) (fun _ _ => Commute.all _ _)

theorem evaluation_tmul (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (x : RESChartRing.Ring B) (y : GammaRVChartPresentation.ChartRing B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) =
      RESOrdinaryReduction.forget B x * GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k y := rfl

def gradedEvaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GradedRingHom (RVBalancedGradings.measuredPiece B) (RESReductionGradings.ordinaryPiece B) :=
  TensorGradedMaps.gradedMap (RVBalancedGradings.measuredData B) (RESReductionGradings.ordinaryCoaction B)
    (evaluation h00 linear hκ hs B hr hγ hΓ k).toRingHom (by
      intro m n x y hx hy
      change evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) ∈ RESReductionGradings.ordinaryPiece B (m + n)
      rw [evaluation_tmul]
      exact SetLike.mul_mem_graded (RESReductionGradings.forget_mem B hx)
        ((GammaOrdinaryEvaluation.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k).map_mem hy))

theorem evaluation_res (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (x : RESChartRing.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (RVFiniteBalancedTensor.resInclusion B x) = RESOrdinaryReduction.forget B x := by
  change evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] 1) = _
  rw [evaluation_tmul, map_one, mul_one]

end DiamondIntegral.Section4.RVOrdinaryTensorEvaluation
