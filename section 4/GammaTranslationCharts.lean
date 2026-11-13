import «section 4».GammaTranslation
import «section 4».GammaChartOperations

/-! Actual compensated translations of partial-volume Gamma charts.
The resulting volume isomorphism is a Gamma-definable bijection; no RV
lift of its translation constants is asserted or required. -/

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters

namespace DiamondIntegral.Section4.GammaTranslationCharts
open GammaWeightedCharts GammaTranslation GammaTupleMaps
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def translatedChart (B : Base (M := M)) {n : ℕ}
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : Chart B n) : Chart B n :=
  GammaChartOperations.ofTotal B n (translated a c.support)
    (translated_definable B a ha c.support c.support_definable)
    (compensatedVolume a c.normalizedVolume)
    (compensatedVolume_definable B a ha c.normalizedVolume c.normalizedVolume_definable)

def translationVolumeIso (B : Base (M := M)) {n : ℕ}
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : Chart B n) : VolumeIso c (translatedChart B a ha c) where
  map := shift a
  graph_definable := graph_definable B c.support c.support_definable (shift a) (shift_coordinates B a ha)
  bijective := shift_bijOn a c.support
  volume_eq := by
    intro u hu
    change c.volume u = compensatedVolume a c.normalizedVolume (shift a u) * (∏ i, shift a u i) / (∏ i, u i)
    rw [← c.normalizedVolume_on u hu]
    exact compensated_volume_eq a c.normalizedVolume u

theorem chartPolynomial_translated (h00 : M ⊨ Axioms.ACVF00)
    (linear : Section2.GammaPiecewiseRationalAffineInput (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : Base (M := M)) (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (hΓ : Section2.NontrivialDefinableGamma B) (k : EulerKind) {n : ℕ}
    (a : Fin n → Values.Gamma (M := M)) (ha : ∀ i, GammaDefinableClosureAtBase B (a i))
    (c : Chart B n) :
    chartPolynomial h00 hκ hs B hr hγ k c = chartPolynomial h00 hκ hs B hr hγ k (translatedChart B a ha c) :=
  chartPolynomial_volumeIso h00 linear hκ hs B hr hγ hΓ k c (translatedChart B a ha c)
    (translationVolumeIso B a ha c)

end DiamondIntegral.Section4.GammaTranslationCharts
