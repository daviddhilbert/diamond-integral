import «section 4».RVCoefficientFunctionTranslationKernel
import «section 4».RVOrdinaryTranslationIdeal

/-! The actual ordinary coefficient-translation ideal is exactly the image
of the proved measured coefficient ideal under forgetting volume. It lies
in the ordinary RV comparison kernel and both Euler kernels. Constant-value
definable functions on the coefficient object also supply its generators.
No reverse kernel inclusion or global RV descent is asserted. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVOrdinaryCoefficientTranslationKernel
open RVMeasuredCharts RVCoordinateScaling RVOrdinaryTranslationIdeal
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def coefficientIdeal (B : Base (M := M)) : Ideal (RVOrdinaryBalancedTensor.Source B) :=
  Ideal.span {x | ∃ k n, ∃ r : RESChart B k, ∃ j : Fin r.arity, ∃ i : Fin n,
    ∃ hp : ∀ u ∈ r.domain, NonzeroRV (u j), ∃ δ : Values.Gamma (M := M),
    ∃ hv : ∀ u ∈ r.domain, codeValue (u j) = δ, ∃ hδ : GammaDefinableClosureAtBase B δ,
    ∃ c : GammaOrdinaryCharts.Chart B n,
      x = generator B r (shiftVector i δ) (shiftVector_definable B i δ hδ) c}

theorem map_measured_coefficientIdeal (B : Base (M := M)) :
    Ideal.map (RVOrdinaryTensorForget.forget B)
      (RVCoefficientCoordinateTranslationKernel.coefficientIdeal B) = coefficientIdeal B := by
  apply le_antisymm
  · rw [RVCoefficientCoordinateTranslationKernel.coefficientIdeal, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro x ⟨y, ⟨k, n, r, j, i, hp, δ, hv, hδ, c, rfl⟩, rfl⟩
    rw [forget_generator]
    exact Ideal.subset_span ⟨k, n, r, j, i, hp, δ, hv, hδ, GammaOrdinaryCharts.ofWeighted c, rfl⟩
  · apply Ideal.span_le.mpr
    rintro x ⟨k, n, r, j, i, hp, δ, hv, hδ, c, rfl⟩
    have hm : RVTranslationIdeals.measuredGenerator B r (shiftVector i δ)
        (shiftVector_definable B i δ hδ) (GammaOrdinaryCharts.toWeighted c) ∈
        RVCoefficientCoordinateTranslationKernel.coefficientIdeal B :=
      Ideal.subset_span ⟨k, n, r, j, i, hp, δ, hv, hδ, GammaOrdinaryCharts.toWeighted c, rfl⟩
    have h := Ideal.mem_map_of_mem (RVOrdinaryTensorForget.forget B) hm
    rw [forget_generator, GammaOrdinaryCharts.ofWeighted_toWeighted] at h
    exact h

theorem coefficientIdeal_le_comparison_ker (B : Base (M := M)) :
    coefficientIdeal B ≤ RingHom.ker (RVOrdinaryBalancedTensor.comparison B).toRingHom := by
  rw [← map_measured_coefficientIdeal]
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change RVOrdinaryBalancedTensor.comparison B (RVOrdinaryTensorForget.forget B x) = 0
  have he := RingHom.congr_fun (RVOrdinaryTensorForget.comparison_square B) x
  change RVOrdinaryBalancedTensor.comparison B (RVOrdinaryTensorForget.forget B x) =
    RVOrdinaryRing.forget B (RVFiniteBalancedTensor.comparison B x) at he
  have hz : RVFiniteBalancedTensor.comparison B x = 0 :=
    RVCoefficientCoordinateTranslationKernel.coefficientIdeal_le_comparison_ker B hx
  rw [hz, map_zero] at he
  exact he

theorem coefficientIdeal_le_translationIdeal (B : Base (M := M)) :
    coefficientIdeal B ≤ translationIdeal B := by
  apply Ideal.span_le.mpr
  rintro x ⟨k, n, r, j, i, hp, δ, hv, hδ, c, rfl⟩
  exact Ideal.subset_span ⟨k, n, r, shiftVector i δ, shiftVector_definable B i δ hδ, c, rfl⟩

theorem coefficientIdeal_homogeneous (B : Base (M := M)) :
    (coefficientIdeal B).IsHomogeneous (RVOrdinaryBalancedGradings.piece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨k, n, r, j, i, hp, δ, hv, hδ, c, rfl⟩
  exact ⟨k + n, (RVOrdinaryBalancedGradings.piece B (k + n)).sub_mem
    (RVOrdinaryBalancedGradings.tmul_mem B (RESOrdinaryGrading.class_mem B r)
      (GammaOrdinaryGrading.class_mem B c))
    (RVOrdinaryBalancedGradings.tmul_mem B (RESOrdinaryGrading.class_mem B r)
      (GammaOrdinaryGrading.class_mem B _))⟩

theorem function_generator_mem (B : Base (M := M)) {k n : ℕ} (r : RESChart B k)
    (f : (Fin r.arity → M) → M)
    (hf : DefinableOverBase B (fun _ : Fin (1 + r.arity) => .rv)
      (RVDefinableGraphExtension.domain r.toChart f))
    (hp : ∀ x ∈ r.domain, NonzeroRV (f x)) (δ : Values.Gamma (M := M))
    (hv : ∀ x ∈ r.domain, codeValue (f x) = δ) (hδ : GammaDefinableClosureAtBase B δ)
    (i : Fin n) (c : GammaOrdinaryCharts.Chart B n) :
    generator B r (shiftVector i δ) (shiftVector_definable B i δ hδ) c ∈ coefficientIdeal B := by
  rw [← map_measured_coefficientIdeal]
  have hm := RVCoefficientFunctionTranslationKernel.measured_generator_mem B r f hf hp δ hv hδ i
    (GammaOrdinaryCharts.toWeighted c)
  have h := Ideal.mem_map_of_mem (RVOrdinaryTensorForget.forget B) hm
  rw [forget_generator, GammaOrdinaryCharts.ofWeighted_toWeighted] at h
  exact h

theorem coefficientIdeal_le_evaluation_ker (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind) :
    coefficientIdeal B ≤ RingHom.ker
      (RVOrdinaryBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ kind).toRingHom :=
  (coefficientIdeal_le_translationIdeal B).trans
    (translationIdeal_le_evaluation_ker h00 linear hκ hs B hr hγ hΓ kind)

end DiamondIntegral.Section4.RVOrdinaryCoefficientTranslationKernel
