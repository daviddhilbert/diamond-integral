import «section 4».RVCoefficientCoordinateTranslation
import «section 4».RVTranslationIdeals

/-! Concrete arbitrary-arity single-coordinate translation relations lie in
the actual measured RV comparison kernel and are annihilated by both
Euler maps. Their generated ideal is homogeneous. This is an inclusion
proved by actual measured RV isomorphisms, not a full kernel presentation. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.RVCoefficientCoordinateTranslationKernel
open RVMeasuredCharts RVCoefficientCoordinateTranslation RVTranslationIdeals RVBalancedGradings RVCoordinateScaling
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem comparison_generator_zero (B : Base (M := M)) {k n : ℕ} (r : RESChart B k) (j : Fin r.arity) (i : Fin n)
    (hp : ∀ x ∈ r.domain, NonzeroRV (x j)) (δ : Values.Gamma (M := M))
    (hv : ∀ x ∈ r.domain, codeValue (x j) = δ) (hδ : GammaDefinableClosureAtBase B δ)
    (c : GammaWeightedCharts.Chart B n) :
    RVFiniteBalancedTensor.comparison B (measuredGenerator B r (shiftVector i δ) (shiftVector_definable B i δ hδ) c) = 0 := by
  have h := RVChartRing.objectClass_iso (iso B r.toChart j i hp δ hv hδ c)
  rw [RVChartRing.objectClass_product, RVChartRing.objectClass_product] at h
  unfold measuredGenerator
  rw [map_sub, RVFiniteBalancedTensor.comparison_tmul, RVFiniteBalancedTensor.comparison_tmul,
    RVChartMaps.ofRES_class]
  have hc : RVSharpRingMap.sharp B (GammaRVChartPresentation.objectClass c) =
      RVChartRing.objectClass (RVSharpCharts.sharpChart c) := RVSharpRingMap.sharp_class B c
  have hd : RVSharpRingMap.sharp B (GammaRVChartPresentation.objectClass (translatedChart B i δ hδ c)) =
      RVChartRing.objectClass (RVSharpCharts.sharpChart (translatedChart B i δ hδ c)) :=
    RVSharpRingMap.sharp_class B (translatedChart B i δ hδ c)
  change RVChartRing.objectClass r.toChart * RVSharpRingMap.sharp B (GammaRVChartPresentation.objectClass c) -
    RVChartRing.objectClass r.toChart * RVSharpRingMap.sharp B (GammaRVChartPresentation.objectClass (translatedChart B i δ hδ c)) = 0
  rw [hc, hd]
  exact sub_eq_zero.mpr h

def coefficientIdeal (B : Base (M := M)) : Ideal (RVFiniteBalancedTensor.Source B) :=
  Ideal.span {x | ∃ k n, ∃ r : RESChart B k, ∃ j : Fin r.arity, ∃ i : Fin n,
    ∃ hp : ∀ u ∈ r.domain, NonzeroRV (u j), ∃ δ : Values.Gamma (M := M),
    ∃ hv : ∀ u ∈ r.domain, codeValue (u j) = δ, ∃ hδ : GammaDefinableClosureAtBase B δ,
    ∃ c : GammaWeightedCharts.Chart B n,
      x = measuredGenerator B r (shiftVector i δ) (shiftVector_definable B i δ hδ) c}

theorem coefficientIdeal_le_comparison_ker (B : Base (M := M)) :
    coefficientIdeal B ≤ RingHom.ker (RVFiniteBalancedTensor.comparison B).toRingHom := by
  apply Ideal.span_le.mpr
  rintro x ⟨k, n, r, j, i, hp, δ, hv, hδ, c, rfl⟩
  exact comparison_generator_zero B r j i hp δ hv hδ c

theorem coefficientIdeal_le_translationIdeal (B : Base (M := M)) : coefficientIdeal B ≤ measuredIdeal B := by
  apply Ideal.span_le.mpr
  rintro x ⟨k, n, r, j, i, hp, δ, hv, hδ, c, rfl⟩
  exact Ideal.subset_span ⟨k, n, r, shiftVector i δ, shiftVector_definable B i δ hδ, c, rfl⟩

theorem coefficientIdeal_homogeneous (B : Base (M := M)) :
    (coefficientIdeal B).IsHomogeneous (measuredPiece B) := by
  apply Ideal.homogeneous_span
  rintro x ⟨k, n, r, j, i, hp, δ, hv, hδ, c, rfl⟩
  exact ⟨k + n, (measuredPiece B (k + n)).sub_mem
    (measured_tmul_mem B (RESRingCoaction.class_mem_gradedPiece B r) (GammaRVGrading.class_mem B c))
    (measured_tmul_mem B (RESRingCoaction.class_mem_gradedPiece B r) (GammaRVGrading.class_mem B _))⟩

theorem coefficientIdeal_le_evaluation_ker (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (B : Base (M := M))
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (kind : EulerKind) :
    coefficientIdeal B ≤ RingHom.ker (RVFiniteBalancedTensor.evaluation h00 linear hκ hs B hr hγ hΓ kind).toRingHom :=
  (coefficientIdeal_le_translationIdeal B).trans
    (measuredIdeal_le_evaluation_ker h00 linear hκ hs B hr hγ hΓ kind)

end DiamondIntegral.Section4.RVCoefficientCoordinateTranslationKernel
