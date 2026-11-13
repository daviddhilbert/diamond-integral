import «section 4».RVDefinableGraphRES
import «section 4».RVCoefficientCoordinateTranslationKernel
import «section 4».RVBoundedCoefficientCoordinateTranslationKernel

/-! Every original-base definable proper RV function of constant value
on a RES coefficient supplies the single-coordinate kernel relation in
arbitrary Gamma arity. Graph adjunction reduces to an actual coefficient
coordinate without changing its RES class. Full and bounded kernels are
handled separately; no complete kernel classification is assumed. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVCoefficientFunctionTranslationKernel
open RVMeasuredCharts RVTranslationIdeals RVCoordinateScaling RVDefinableGraphRES FiniteTupleBlocks
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (B : Base (M := M)) {k n : ℕ} (r : RESChart B k) (f : (Fin r.arity → M) → M)
variable (hf : DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv) (RVDefinableGraphExtension.domain r.toChart f))
variable (hp : ∀ x ∈ r.domain, NonzeroRV (f x)) (δ : Values.Gamma (M := M))
variable (hv : ∀ x ∈ r.domain, codeValue (f x) = δ) (hδ : GammaDefinableClosureAtBase B δ) (i : Fin n)
include hf hp hv

theorem measured_generator_mem (c : GammaWeightedCharts.Chart B n) :
    measuredGenerator B r (shiftVector i δ) (shiftVector_definable B i δ hδ) c ∈
      RVCoefficientCoordinateTranslationKernel.coefficientIdeal B := by
  let g := resChart r f hf hp δ hv
  let j : Fin g.arity := tailIndex 1 r.arity 0
  have hp' : ∀ u ∈ g.domain, NonzeroRV (u j) := by
    intro u hu
    change NonzeroRV (u (tailIndex 1 r.arity 0))
    rw [last_eq r.toChart f u hu]
    exact hp _ hu.1
  have hv' : ∀ u ∈ g.domain, codeValue (u j) = δ := by
    intro u hu
    change codeValue (u (tailIndex 1 r.arity 0)) = δ
    rw [last_eq r.toChart f u hu]
    exact hv _ hu.1
  have hc : RESChartRing.objectClass g = RESChartRing.objectClass r := measured_class r f hf hp δ hv
  have he : measuredGenerator B r (shiftVector i δ) (shiftVector_definable B i δ hδ) c =
      measuredGenerator B g (shiftVector i δ) (shiftVector_definable B i δ hδ) c := by
    unfold measuredGenerator
    rw [hc]
  rw [he]
  exact Ideal.subset_span ⟨k, n, g, j, i, hp', δ, hv', hδ, c, rfl⟩

theorem bounded_generator_mem (c : GammaBoundedRVCharts.BoundedChart B n) :
    boundedGenerator B r (shiftVector i δ) (shiftVector_definable B i δ hδ) c ∈
      RVBoundedCoefficientCoordinateTranslationKernel.coefficientIdeal B := by
  let g := resChart r f hf hp δ hv
  let j : Fin g.arity := tailIndex 1 r.arity 0
  have hp' : ∀ u ∈ g.domain, NonzeroRV (u j) := by
    intro u hu
    change NonzeroRV (u (tailIndex 1 r.arity 0))
    rw [last_eq r.toChart f u hu]
    exact hp _ hu.1
  have hv' : ∀ u ∈ g.domain, codeValue (u j) = δ := by
    intro u hu
    change codeValue (u (tailIndex 1 r.arity 0)) = δ
    rw [last_eq r.toChart f u hu]
    exact hv _ hu.1
  have hc : RESChartRing.objectClass g = RESChartRing.objectClass r := measured_class r f hf hp δ hv
  have he : boundedGenerator B r (shiftVector i δ) (shiftVector_definable B i δ hδ) c =
      boundedGenerator B g (shiftVector i δ) (shiftVector_definable B i δ hδ) c := by
    unfold boundedGenerator
    rw [hc]
  rw [he]
  exact Ideal.subset_span ⟨k, n, g, j, i, hp', δ, hv', hδ, c, rfl⟩

theorem measured_comparison_zero (c : GammaWeightedCharts.Chart B n) :
    RVFiniteBalancedTensor.comparison B
      (measuredGenerator B r (shiftVector i δ) (shiftVector_definable B i δ hδ) c) = 0 :=
  RVCoefficientCoordinateTranslationKernel.coefficientIdeal_le_comparison_ker B
    (measured_generator_mem B r f hf hp δ hv hδ i c)

theorem bounded_comparison_zero (c : GammaBoundedRVCharts.BoundedChart B n) :
    RVBoundedBalancedTensor.comparison B
      (boundedGenerator B r (shiftVector i δ) (shiftVector_definable B i δ hδ) c) = 0 :=
  RVBoundedCoefficientCoordinateTranslationKernel.coefficientIdeal_le_comparison_ker B
    (bounded_generator_mem B r f hf hp δ hv hδ i c)

end DiamondIntegral.Section4.RVCoefficientFunctionTranslationKernel
