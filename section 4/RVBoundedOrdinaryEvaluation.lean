import «section 4».RVBoundedTensorComparison
import «section 4».GammaEulerBoundedComparison

/-! Direct bounded ordinary evaluation on the actual balanced tensor.
Bounded Euler comparison proves independence of Euler choice without a
canonical-structure assumption. Agreement with the older profile-range
construction is proved when that construction's premise is available. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open scoped TensorProduct

namespace DiamondIntegral.Section4.RVBoundedOrdinaryEvaluation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def evaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    RVBoundedBalancedTensor.Source B →ₐ[GammaFiniteRVPresentation.ChartRing B] RESOrdinaryReduction.ReducedRing B :=
  (RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k).comp (RVBoundedTensorComparison.toFull B)

theorem evaluation_tmul (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind)
    (x : RESChartRing.Ring B) (y : GammaBoundedRVPresentation.ChartRing B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y) =
      RESOrdinaryReduction.forget B x * GammaOrdinaryEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k (GammaBoundedRVMaps.forget B y) := by
  change RVOrdinaryTensorEvaluation.evaluation h00 linear hκ hs B hr hγ hΓ k
    (RVBoundedTensorComparison.toFull B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y)) = _
  rw [RVBoundedTensorComparison.toFull_tmul, RVOrdinaryTensorEvaluation.evaluation_tmul]

def gradedEvaluation (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    GradedRingHom (RVBalancedGradings.boundedPiece B) (RESReductionGradings.ordinaryPiece B) :=
  (RVOrdinaryTensorEvaluation.gradedEvaluation h00 linear hκ hs B hr hγ hΓ k).comp (RVBoundedTensorComparison.gradedToFull B)

theorem evaluation_independent_kind (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k l : EulerKind) :
    evaluation h00 linear hκ hs B hr hγ hΓ k = evaluation h00 linear hκ hs B hr hγ hΓ l := by
  apply Algebra.TensorProduct.ext'
  intro x y
  rw [evaluation_tmul, evaluation_tmul]
  exact congrArg (RESOrdinaryReduction.forget B x * ·)
    (RingHom.congr_fun (GammaEulerEvaluation.bounded_independent_kind h00 linear hκ hs B hr hγ hΓ k l
      (RESOrdinaryReduction.torusClass B)) y)

theorem evaluation_res (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) (x : RESChartRing.Ring B) :
    evaluation h00 linear hκ hs B hr hγ hΓ k (RVBoundedBalancedTensor.resInclusion B x) = RESOrdinaryReduction.forget B x := by
  change evaluation h00 linear hκ hs B hr hγ hΓ k (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] 1) = _
  rw [evaluation_tmul, map_one, map_one, mul_one]

theorem evaluation_eq_previous (hc : CanonicalStructure.IsCanonical (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) :
    evaluation h00 linear hκ hs B hr hγ hΓ k = RVBoundedBalancedTensor.evaluation hc h00 linear hκ hs B hr hγ hΓ k :=
  RVBoundedTensorComparison.evaluation_square hc h00 linear hκ hs B hr hγ hΓ k

end DiamondIntegral.Section4.RVBoundedOrdinaryEvaluation
