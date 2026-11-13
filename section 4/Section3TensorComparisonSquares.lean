import «section 4».Section3TensorRingEquivalences
import «section 4».Section3RVComparisonSquares
import «section 4».CompletionTensorMapFormula

/-! The actual balanced tensor comparisons commute with the source and
target equivalences in both ordinary and measured settings. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open DiamondIntegral.Section3
open scoped TensorProduct

namespace DiamondIntegral.Section4.Section3TensorComparisonSquares
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (B : Base (M := M))
attribute [local instance] gammaGroundUnmeasuredTensorGammaRing gammaGroundUnmeasuredTensorFiniteGammaRing
  gammaGroundUnmeasuredTensorRVRing gammaGroundMeasuredTensorGammaRing
  gammaGroundMeasuredTensorFiniteGammaRing gammaGroundMeasuredTensorRVRing

theorem ordinary_native_tmul (x : Section3RESClassCuts.OrdinaryRing hc B) (y : GammaGroundGammaGrothendieckRing hc B) :
    gammaGroundUnmeasuredGroupTensorMap (x ⊗ₜ[GammaGroundFiniteGammaGrothendieckRing hc B] y) =
      ringCompletionMap gammaGroundRESToRVSemiring x * ringCompletionMap gammaGroundGammaToRVSemiring y :=
  CompletionTensorMapFormula.completed_tmul gammaGroundRESToRVSemiring gammaGroundGammaToRVSemiring
    gammaGroundFiniteGamma_semiring_square x y

theorem measured_native_tmul (x : Section3RESClassCuts.MeasuredRing hc B) (y : GammaGroundMeasuredGammaGrothendieckRing hc B) :
    gammaGroundMeasuredGroupTensorMap (x ⊗ₜ[GammaGroundMeasuredFiniteGammaGrothendieckRing hc B] y) =
      ringCompletionMap gammaGroundMeasuredRESToRVSemiring x * ringCompletionMap gammaGroundMeasuredGammaToRVSemiring y :=
  CompletionTensorMapFormula.completed_tmul gammaGroundMeasuredRESToRVSemiring gammaGroundMeasuredGammaToRVSemiring
    gammaGroundMeasuredFiniteGamma_semiring_square x y

theorem ordinary_square :
    (gammaGroundUnmeasuredGroupTensorMap (hc := hc) (ground := B)).comp (Section3TensorRingEquivalences.ordinary hc B).toRingHom =
      (Section3RVRingEquivalences.ordinary hc B).toRingHom.comp (RVOrdinaryBalancedTensor.comparison B).toRingHom := by
  apply RingTensorCongruence.hom_ext
  intro x y
  change gammaGroundUnmeasuredGroupTensorMap (Section3TensorRingEquivalences.ordinary hc B (x ⊗ₜ[GammaOrdinaryFiniteRing.Ring B] y)) =
    Section3RVRingEquivalences.ordinary hc B (RVOrdinaryBalancedTensor.comparison B (x ⊗ₜ[GammaOrdinaryFiniteRing.Ring B] y))
  rw [Section3TensorRingEquivalences.ordinary_tmul, ordinary_native_tmul, RVOrdinaryBalancedTensor.comparison_tmul, map_mul]
  exact congrArg₂ (· * ·) (RingHom.congr_fun (Section3RVComparisonSquares.ordinary_res hc B) x).symm
    (RingHom.congr_fun (Section3RVComparisonSquares.ordinary_gamma hc B) y).symm

theorem measured_square :
    (gammaGroundMeasuredGroupTensorMap (hc := hc) (ground := B)).comp (Section3TensorRingEquivalences.measured hc B).toRingHom =
      (Section3RVRingEquivalences.measured hc B).toRingHom.comp (RVFiniteBalancedTensor.comparison B).toRingHom := by
  apply RingTensorCongruence.hom_ext
  intro x y
  change gammaGroundMeasuredGroupTensorMap (Section3TensorRingEquivalences.measured hc B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y)) =
    Section3RVRingEquivalences.measured hc B (RVFiniteBalancedTensor.comparison B (x ⊗ₜ[GammaFiniteRVPresentation.ChartRing B] y))
  rw [Section3TensorRingEquivalences.measured_tmul, measured_native_tmul, RVFiniteBalancedTensor.comparison_tmul, map_mul]
  exact congrArg₂ (· * ·) (RingHom.congr_fun (Section3RVComparisonSquares.measured_res hc B) x).symm
    (RingHom.congr_fun (Section3RVComparisonSquares.measured_gamma hc B) y).symm

theorem ordinary (x : RVOrdinaryBalancedTensor.Source B) :
    gammaGroundUnmeasuredGroupTensorMap (Section3TensorRingEquivalences.ordinary hc B x) =
      Section3RVRingEquivalences.ordinary hc B (RVOrdinaryBalancedTensor.comparison B x) := RingHom.congr_fun (ordinary_square hc B) x
theorem measured (x : RVFiniteBalancedTensor.Source B) :
    gammaGroundMeasuredGroupTensorMap (Section3TensorRingEquivalences.measured hc B x) =
      Section3RVRingEquivalences.measured hc B (RVFiniteBalancedTensor.comparison B x) := RingHom.congr_fun (measured_square hc B) x

end DiamondIntegral.Section4.Section3TensorComparisonSquares
